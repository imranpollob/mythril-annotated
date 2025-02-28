"""This module contains the detection code for predictable variable
dependence."""

import logging
from typing import List, cast

from mythril.analysis import solver
from mythril.analysis.issue_annotation import IssueAnnotation
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.analysis.module.module_helpers import is_prehook
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import TIMESTAMP_DEPENDENCE, WEAK_RANDOMNESS
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import ULT, And, symbol_factory

log = logging.getLogger(__name__)

predictable_ops = ["COINBASE", "GASLIMIT", "TIMESTAMP", "NUMBER"]

'''This module is designed to detect when control flow in a smart contract depends on predictable environment variables (such as block.coinbase, block.gaslimit, block.timestamp or block.number). If the contract’s jump conditions (or other decisions) are influenced by such variables, an issue is reported. There are two main types of annotations used:

PredictableValueAnnotation: Marks a symbolic variable that was initialized from a predictable environment variable.
OldBlockNumberUsedAnnotation: Marks a case when an old block number (or block hash) is used.'''

class PredictableValueAnnotation:
    """Symbol annotation used if a variable is initialized from a predictable environment variable."""

    def __init__(self, operation: str) -> None:
        '''Stores the value of operation for later use'''
        self.operation = operation


class OldBlockNumberUsedAnnotation(StateAnnotation):
    """Symbol annotation used if a variable is initialized from a predictable environment variable."""

    def __init__(self) -> None:
        pass


class PredictableVariables(DetectionModule):
    """This module detects whether control flow decisions are made using predictable
    parameters."""

    name = "Control flow depends on a predictable environment variable"
    swc_id = "{} {}".format(TIMESTAMP_DEPENDENCE, WEAK_RANDOMNESS)
    description = (
        "Check whether control flow decisions are influenced by block.coinbase,"
        "block.gaslimit, block.timestamp or block.number."
    )
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["JUMPI", "BLOCKHASH"]
    post_hooks = ["BLOCKHASH"] + predictable_ops

    def _execute(self, state: GlobalState) -> List[Issue]:
        """

        :param state:
        :return:
        """
        return self._analyze_state(state)

    '''Parameter state represents the current symbolic global state of the EVM.
    It returns a list of Issue objects – each representing a detected vulnerability.'''
    def _analyze_state(self, state: GlobalState) -> List[Issue]:
        """

        :param state:
        :return:
        """

        issues = []

        '''Checks if the analysis is currently in a pre-hook context. A “pre-hook” generally means before the opcode is executed.'''
        if is_prehook():
            '''Retrieves the opcode of the current instruction from the state. This tells us what operation is being executed (e.g., "JUMPI" or "BLOCKHASH")'''
            opcode = state.get_current_instruction()["opcode"]

            if opcode == "JUMPI":
                # Look for predictable state variables in jump condition

                '''Iterates over the annotations of the second-to-top element on the EVM stack. In a typical JUMPI, the condition is often the second element on the stack'''
                for annotation in state.mstate.stack[-2].annotations:
                    if isinstance(annotation, PredictableValueAnnotation):
                        '''Retrieves the current set of constraints from the global state. These constraints define the conditions under which the state is reached.'''
                        constraints = state.world_state.constraints
                        try:
                            '''Attempts to generate a concrete transaction sequence for the state given the constraints'''
                            transaction_sequence = solver.get_transaction_sequence(
                                state, constraints
                            )
                        except UnsatError:
                            '''If the constraints are unsatisfiable (raising an UnsatError), skip this annotation'''
                            continue
                        description = (
                            annotation.operation
                            + " is used to determine a control flow decision. "
                        )
                        description += (
                            "Note that the values of variables like coinbase, gaslimit, block number and timestamp are "
                            "predictable and can be manipulated by a malicious miner. Also keep in mind that "
                            "attackers know hashes of earlier blocks. Don't use any of those environment variables "
                            "as sources of randomness and be aware that use of these variables introduces "
                            "a certain level of trust into miners."
                        )

                        """
                        Usually report low severity except in cases where the hash of a previous block is used to
                        determine control flow. 
                        """

                        severity = "Low"

                        swc_id = (
                            TIMESTAMP_DEPENDENCE
                            if "timestamp" in annotation.operation
                            else WEAK_RANDOMNESS
                        )

                        issue = Issue(
                            contract=state.environment.active_account.contract_name,
                            function_name=state.environment.active_function_name,
                            address=state.get_current_instruction()["address"],
                            swc_id=swc_id,
                            bytecode=state.environment.code.bytecode,
                            title="Dependence on predictable environment variable",
                            severity=severity,
                            description_head="A control flow decision is made based on {}.".format(
                                annotation.operation
                            ),
                            description_tail=description,
                            gas_used=(
                                state.mstate.min_gas_used,
                                state.mstate.max_gas_used,
                            ),
                            transaction_sequence=transaction_sequence,
                        )
                        state.annotate(
                            IssueAnnotation(
                                conditions=[And(*constraints)],
                                issue=issue,
                                detector=self,
                            )
                        )
                        issues.append(issue)

            elif opcode == "BLOCKHASH":
                param = state.mstate.stack[-1]

                '''First constraint: ULT(param, state.environment.block_number) ensures that the block number parameter (param) is less than the current block number.
                Second constraint: Ensures that the current block number is less than 2**255, preventing an overflow which might occur in the solver.'''
                constraint = [
                    ULT(param, state.environment.block_number),
                    ULT(
                        state.environment.block_number,
                        symbol_factory.BitVecVal(2**255, 256),
                    ),
                ]

                # Why the second constraint? Because without it Z3 returns a solution where param overflows.

                try:
                    '''Tries to obtain a model with the combined current constraints plus the new constraint.'''
                    solver.get_model(
                        state.world_state.constraints + constraint  # type: ignore
                    )
                    '''If successful, it then annotates the state'''
                    state.annotate(OldBlockNumberUsedAnnotation())

                except UnsatError:
                    pass

        else:
            # we're in post hook

            '''Retrieves the opcode of the last executed instruction. This is done by accessing the instruction list at position pc - 1 (where pc is the program counter).'''
            opcode = state.environment.code.instruction_list[state.mstate.pc - 1][
                "opcode"
            ]

            if opcode == "BLOCKHASH":
                # if we're in the post hook of a BLOCKHASH op, check if an old block number was used to create it.
                '''Uses cast to ensure these annotations are seen as a list of OldBlockNumberUsedAnnotation.'''
                annotations = cast(
                    List[OldBlockNumberUsedAnnotation],
                    list(state.get_annotations(OldBlockNumberUsedAnnotation)),
                )

                if len(annotations):
                    # We can append any block constraint here
                    state.mstate.stack[-1].annotate(
                        PredictableValueAnnotation("The block hash of a previous block")
                    )
            else:
                # Always create an annotation when COINBASE, GASLIMIT, TIMESTAMP or NUMBER is executed.

                state.mstate.stack[-1].annotate(
                    PredictableValueAnnotation(
                        "The block.{} environment variable".format(opcode.lower())
                    )
                )

        return issues


detector = PredictableVariables()
