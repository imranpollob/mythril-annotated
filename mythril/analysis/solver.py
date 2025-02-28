"""This module contains analysis module helpers to solve path constraints."""

import logging
from typing import Any, Dict, List, Tuple, Union

import z3
from z3 import FuncInterp

from mythril.exceptions import UnsatError
from mythril.laser.ethereum.function_managers import (
    keccak_function_manager,
)
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction import BaseTransaction
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.laser.smt import UGE, symbol_factory
from mythril.support.model import get_model

log = logging.getLogger(__name__)
z3.set_option(
    max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000
)


'''This module provides helper functions for interacting with the Z3 SMT solver to solve path constraints generated during symbolic execution. 
Its main purpose is to convert symbolic execution traces into concrete transaction sequences by finding solutions to the constraints accumulated along those paths.
'''

'''SMT Solver: An SMT (Satisfiability Modulo Theories) solver is a tool that can determine whether a set of logical formulas (constraints) has a solution. Z3 is a popular and powerful SMT solver.

Path Constraints: During symbolic execution, the tool tracks the conditions that must be true for a specific execution path to be taken. These conditions are expressed as logical formulas and are known as path constraints.

Concrete Execution: Symbolic execution generates symbolic states that are defined based on logical constraints. In order to create real transactions that trigger vulnerabilities, these symbolic states must be converted into real states by plugging in concrete (i.e. real) values to variables.'''

'''Provides a human-readable representation of a Z3 model,'''
def pretty_print_model(model):
    """Pretty prints a z3 model
    
    The pretty_print_model function is a utility function designed to make it easier to inspect and debug Z3 models in a human-readable format. When working with symbolic execution and constraint solving, Z3 models can contain complex data structures, including symbolic variables, function interpretations, and constraints. The pretty_print_model function simplifies the process of understanding these models by formatting them in a clear and concise way.

    :param model:
    :return:
    """
    ret = ""

    for d in model.decls():
        if isinstance(model[d], FuncInterp):
            condition = model[d].as_list()
            ret += "%s: %s\n" % (d.name(), condition)
            continue

        try:
            condition = "0x%x" % model[d].as_long()
        except:
            condition = str(z3.simplify(model[d]))

        ret += "%s: %s\n" % (d.name(), condition)

    return ret


'''Generates a concrete transaction sequence that satisfies the given constraints, starting from a symbolic execution state.'''
def get_transaction_sequence(
    global_state: GlobalState, constraints: Constraints
) -> Dict[str, Any]:
    """Generate concrete transaction sequence.
    Note: This function only considers the constraints in constraint argument,
    which in some cases is expected to differ from global_state's constraints

    :param global_state: GlobalState to generate transaction sequence for
    :param constraints: list of constraints used to generate transaction sequence
    
    Logic:
    1. Extracts the transaction sequence from the global_state.
    2. Sets minimisation constraints using _set_minimisation_constraints.
    3. Adds constraints to minimize calldata size and value.
    4. Ensures accounts have sufficient balances.
    5. Uses the Z3 SMT solver (through the get_model function from mythril.support.model) to find a concrete model (a solution) that satisfies the constraints. If the model is unsat, it throws the UnsatError.
    6. Iterates through the symbolic transactions in the sequence and converts them into concrete transactions using _get_concrete_transaction. This involves evaluating symbolic variables (such as function inputs, transfer amounts, and account balances) in the model to obtain concrete values.
    7. Replaces symbolic SHA3 hashes in the input with concrete values using _replace_with_actual_sha.
    8. Adds a calldata placeholder to the concrete transactions with _add_calldata_placeholder.
    9. Returns a dictionary containing the initial state and the transaction sequence, all populated with concrete values.
    """
    # Extracts the transaction sequence from the global state.
    transaction_sequence = global_state.world_state.transaction_sequence
    concrete_transactions = []
    # Adds minimization constraints (e.g., minimizing calldata size and call value).
    tx_constraints, minimize = _set_minimisation_constraints(
        transaction_sequence, constraints.copy(), [], 5000, global_state.world_state
    )

    try:
        model = get_model(tx_constraints, minimize=minimize)
    except UnsatError:
        raise UnsatError

    if isinstance(transaction_sequence[0], ContractCreationTransaction):
        initial_world_state = transaction_sequence[0].prev_world_state
    else:
        initial_world_state = transaction_sequence[0].world_state

    initial_accounts = initial_world_state.accounts

    for transaction in transaction_sequence:
        concrete_transaction = _get_concrete_transaction(model, transaction)
        concrete_transactions.append(concrete_transaction)

    min_price_dict: Dict[str, int] = {}
    for address in initial_accounts.keys():
        min_price_dict[address] = model.eval(
            initial_world_state.starting_balances[
                symbol_factory.BitVecVal(address, 256)
            ].raw,
            model_completion=True,
        ).as_long()

    concrete_initial_state = _get_concrete_state(initial_accounts, min_price_dict)
    if isinstance(transaction_sequence[0], ContractCreationTransaction):
        code = transaction_sequence[0].code
        _replace_with_actual_sha(concrete_transactions, model, code)
    else:
        _replace_with_actual_sha(concrete_transactions, model)
    _add_calldata_placeholder(concrete_transactions, transaction_sequence)
    steps = {"initialState": concrete_initial_state, "steps": concrete_transactions}

    return steps

'''Adds a "calldata" key to each concrete transaction dictionary, populating it with the "input" data. This is necessary because some parts of Mythril expect transactions to have explicit "calldata" fields. Additionally, it removes the contract code in the calldata for contract creation'''
def _add_calldata_placeholder(
    concrete_transactions: List[Dict[str, str]],
    transaction_sequence: List[BaseTransaction],
):
    """
    Adds a calldata placeholder into the concrete transactions
    :param concrete_transactions:
    :param transaction_sequence:
    :return:
    """
    for tx in concrete_transactions:
        tx["calldata"] = tx["input"]
    if not isinstance(transaction_sequence[0], ContractCreationTransaction):
        return

    if isinstance(transaction_sequence[0].code.bytecode, tuple):
        code_len = len(transaction_sequence[0].code.bytecode) * 2
    else:
        code_len = len(transaction_sequence[0].code.bytecode)
    concrete_transactions[0]["calldata"] = concrete_transactions[0]["input"][
        code_len + 2 :
    ]

'''Replace all symbolic sha values on the input field with concrete values'''
def _replace_with_actual_sha(
    concrete_transactions: List[Dict[str, str]], model: z3.Model, code=None
):
    '''retrieve precomputed Keccak-256 hashes from the symbolic execution model.
    This function stores previously computed hashes and their inverse mappings, which will be used to replace symbolic values in transactions.'''
    concrete_hashes = keccak_function_manager.get_concrete_hash_data(model)
    for tx in concrete_transactions:
        if keccak_function_manager.hash_matcher not in tx["input"]:
            continue
        if code is not None and code.bytecode in tx["input"]:
            s_index = len(code.bytecode) + 2
        else:
            s_index = 10
        for i in range(s_index, len(tx["input"])):
            data_slice = tx["input"][i : i + 64]
            if (
                keccak_function_manager.hash_matcher not in data_slice
                or len(data_slice) != 64
            ):
                continue
            find_input = symbol_factory.BitVecVal(int(data_slice, 16), 256)
            input_ = None
            for size in concrete_hashes:
                _, inverse = keccak_function_manager.store_function[size]
                if find_input.value not in concrete_hashes[size]:
                    continue
                input_ = symbol_factory.BitVecVal(
                    model.eval(inverse(find_input).raw).as_long(), size
                )

            if input_ is None:
                continue
            keccak = keccak_function_manager.find_concrete_keccak(input_)
            hex_keccak = hex(keccak.value)[2:]
            if len(hex_keccak) != 64:
                hex_keccak = "0" * (64 - len(hex_keccak)) + hex_keccak
            tx["input"] = tx["input"][:s_index] + tx["input"][s_index:].replace(
                tx["input"][i : 64 + i], hex_keccak
            )

'''Extracts concrete account states from a symbolic execution environment.'''
def _get_concrete_state(
    initial_accounts: Dict, min_price_dict: Dict[str, int]
) -> Dict[str, Dict]:
    """Gets a concrete state"""
    accounts = {}
    for address, account in initial_accounts.items():
        # Skip empty default account

        data: Dict[str, Union[int, str]] = {}
        data["nonce"] = account.nonce # The transaction count of the account.
        data["code"] = account.serialised_code() # The contract bytecode (if it’s a smart contract) or empty if it’s an EOA
        data["storage"] = str(account.storage) # The contract’s storage (converted to a string for serialization).
        data["balance"] = hex(min_price_dict.get(address, 0)) # The ETH balance of the account, retrieved from min_price_dict
        accounts[hex(address)] = data
    return {"accounts": accounts}


'''Converts a symbolic transaction into a concrete transaction by evaluating symbolic variables in a Z3 model.'''
def _get_concrete_transaction(model: z3.Model, transaction: BaseTransaction):
    """Gets a concrete transaction from a transaction and z3 model"""
    # Get concrete values from transaction
    # Retrieves the recipient (callee/Receiver) of the transaction.
    address = hex(transaction.callee_account.address.value)
    # Uses Z3’s model evaluator (model.eval()) to determine the concrete ETH (call_value) being sent.
    value = model.eval(transaction.call_value.raw, model_completion=True).as_long()
    # Resolve the Caller (Sender)
    caller = "0x" + (
        "%x" % model.eval(transaction.caller.raw, model_completion=True).as_long()
    ).zfill(40)

    '''Handle Contract Creation Transactions
    If the transaction is creating a contract, it:
    Removes the recipient address (since it’s not calling an existing contract).
    Includes the contract bytecode in input_, as this is the data needed for contract deployment.'''
    input_ = ""
    if isinstance(transaction, ContractCreationTransaction):
        address = ""
        input_ += transaction.code.bytecode

    # Extract and Format Calldata (Function Inputs)
    # Converts it into hex format for execution.
    input_ += "".join(
        [
            hex(b)[2:] if len(hex(b)) % 2 == 0 else "0" + hex(b)[2:]
            for b in transaction.call_data.concrete(model)
        ]
    )

    # Create concrete transaction dict
    concrete_transaction: Dict[str, str] = dict()
    # Encoded function parameters or contract bytecode.
    concrete_transaction["input"] = "0x" + input_
    # Amount of ETH sent.
    concrete_transaction["value"] = "0x%x" % value
    # Fixme: base origin assignment on origin symbol
    # Sender address.
    concrete_transaction["origin"] = caller
    # Receiver address.
    concrete_transaction["address"] = "%s" % address

    return concrete_transaction

'''Set constraints that minimise key transaction values'''
def _set_minimisation_constraints(
    transaction_sequence, constraints, minimize, max_size, world_state
) -> Tuple[Constraints, tuple]:
    """Set constraints that minimise key transaction values

    Constraints generated:
    - Upper bound on calldata size
    - Minimisation of call value's and calldata sizes

    :param transaction_sequence: Transaction for which the constraints should be applied
    :param constraints: The constraints array which should contain any added constraints
    :param minimize: The minimisation array which should contain any variables that should be minimised
    :param max_size: The max size of the calldata array
    :return: updated constraints, minimize
    """
    for transaction in transaction_sequence:
        '''Set upper bound on calldata size
        Without an upper bound, the solver might generate extremely large calldata, which can lead to:
        Unnecessary computational complexity.
        Unrealistic test cases that don’t reflect real-world transactions.'''
        max_calldata_size = symbol_factory.BitVecVal(max_size, 256)
        constraints.append(UGE(max_calldata_size, transaction.call_data.calldatasize))

        # Minimize
        '''Smart contract transactions often involve call_value (ETH sent in a transaction) and calldatasize (data input).
        In many attack scenarios, minimal input values can be just as effective as large ones.
        Minimizing these values allows Mythril to:
        Find vulnerabilities faster (smaller search space for the solver).
        Generate more efficient test cases (avoiding unnecessarily large calldata).'''
        minimize.append(transaction.call_data.calldatasize)
        minimize.append(transaction.call_value)
        constraints.append(
            UGE(
                symbol_factory.BitVecVal(1000000000000000000000, 256),
                world_state.starting_balances[transaction.caller],
            )
        )

    '''Ensuring Caller Has Sufficient Balance. Preventing Unrealistic Account Balances.z
    If a caller (EOA or contract) doesn’t have enough balance, a transaction sending ETH (call_value) could be invalid.'''
    for account in world_state.accounts.values():
        # Lazy way to prevent overflows and to ensure "reasonable" balances
        # Each account starts with less than 100 ETH
        constraints.append(
            UGE(
                symbol_factory.BitVecVal(100000000000000000000, 256),
                world_state.starting_balances[account.address],
            )
        )

    return constraints, tuple(minimize)
