"""This module contains the detection code for Arbitrary jumps."""

import logging # module for logging messages.

from mythril.analysis.issue_annotation import IssueAnnotation # used to attach an issue to a global state
from mythril.analysis.module.base import DetectionModule, EntryPoint, Issue
from mythril.analysis.solver import UnsatError, get_transaction_sequence
from mythril.analysis.swc_data import ARBITRARY_JUMP
from mythril.laser.ethereum.state.global_state import GlobalState # Imports the GlobalState class, representing the state of the EVM
from mythril.laser.smt import And, BitVec, symbol_factory # Imports symbolic data types and functions from Mythril's SMT module.
from mythril.support.model import get_model # Imports get_model to obtain a solution to SMT expressions.

log = logging.getLogger(__name__) # initializes the logger

DESCRIPTION = """

Search for jumps to arbitrary locations in the bytecode
"""

'''The function determines if the symbolic jump destination has only one concrete solution under the current constraints.

jump_dest: a symbolic bit vector (of type BitVec) representing the jump destination.
state: an instance of GlobalState that holds the current symbolic state and its constraints.
'''
def is_unique_jumpdest(jump_dest: BitVec, state: GlobalState) -> bool:
    """
    Handles cases where jump_dest evaluates to a single concrete value
    """

    try:
        '''we attempt to obtain a model of the current execution constraints from the world state'''
        model = get_model(state.world_state.constraints)
    except UnsatError:
        '''If these constraints are unsatisfiable (i.e. no model exists) an UnsatError is raised. In that case, we return True, indicating that the jump destination is unique'''
        return True
    
    '''Once we have a model, we evaluate the raw symbolic expression of jump_dest using the solver model.
    The call to model.eval(jump_dest.raw, model_completion=True) forces the solver to choose a concrete value for jump_dest.
    The result, stored in concrete_jump_dest, represents the specific jump destination according to the current model.'''
    concrete_jump_dest = model.eval(jump_dest.raw, model_completion=True)
    
    try:
        # test if an alternative solution exists
        '''This constraint forces the jump destination to be different from the concrete value we just computed.
        The expression concrete_jump_dest.as_long() converts the evaluated value into a concrete integer, and then symbol_factory.BitVecVal(..., 256) creates a new bit vector with that concrete value.
        If adding this inequality constraint makes the constraints unsatisfiable (i.e. no model exists where jump_dest differs from the computed value), an UnsatError is raised. In this case, we return True meaning that the jump destination is unique—it cannot take on any value other than the one computed.'''
        model = get_model(
            state.world_state.constraints
            + [symbol_factory.BitVecVal(concrete_jump_dest.as_long(), 256) != jump_dest]
        )
    except UnsatError:
        return True
    return False


class ArbitraryJump(DetectionModule):
    """This module searches for JUMPs to a user-specified location."""

    name = "Caller can redirect execution to arbitrary bytecode locations"
    swc_id = ARBITRARY_JUMP
    description = DESCRIPTION
    entry_point = EntryPoint.CALLBACK # We want to be notified when the callback happens
    pre_hooks = ["JUMP", "JUMPI"] # A list containing all instructions the module will look for.

    def reset_module(self):
        """
        Resets the module by clearing everything
        :return:
        """
        super().reset_module()

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        return self._analyze_state(state)

    def _analyze_state(self, state):
        """

        :param state:
        :return:
        """

        '''Retrieves the top-most element from the EVM’s stack (from the current machine state) as the jump destination. This is the value that the program will jump to if executed.'''
        jump_dest = state.mstate.stack[-1]

        if jump_dest.symbolic is False:
            ''' If the destination is concrete, nothing suspicious is happening; thus, the analysis returns an empty list (no issues found).'''
            return []

        '''Calls the helper is_unique_jumpdest to check if there is only one possible value for the jump destination given the constraints.'''
        if is_unique_jumpdest(jump_dest, state) is True:
            '''If the jump destination is unique (cannot be deviated), the module does not detect a vulnerability and returns an empty list.'''
            return []

        try:
            '''Calls get_transaction_sequence with the current state and its constraints to generate a sequence of transactions that concretely exercise the state.'''
            transaction_sequence = get_transaction_sequence(
                state, state.world_state.constraints
            )
        except UnsatError:
            return []

        log.info("Detected arbitrary jump dest")

        issue = Issue(
            contract=state.environment.active_account.contract_name,
            function_name=state.environment.active_function_name,
            address=state.get_current_instruction()["address"],
            swc_id=ARBITRARY_JUMP,
            title="Jump to an arbitrary instruction",
            severity="High",
            bytecode=state.environment.code.bytecode,
            description_head="The caller can redirect execution to arbitrary bytecode locations.",
            description_tail="It is possible to redirect the control flow to arbitrary locations in the code. "
            "This may allow an attacker to bypass security controls or manipulate the business logic of the "
            "smart contract. Avoid using low-level-operations and assembly to prevent this issue.",
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            transaction_sequence=transaction_sequence,
        )
        
        '''Annotates the current global state with the generated issue.'''
        state.annotate(
            IssueAnnotation(
                conditions=[And(*state.world_state.constraints)],
                issue=issue,
                detector=self,
            )
        )

        return [issue]


detector = ArbitraryJump()
