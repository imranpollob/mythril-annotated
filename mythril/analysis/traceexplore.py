"""This module provides a function to convert a state space into a set of state
nodes and transition edges."""

import re

from z3 import Z3Exception

from mythril.laser.ethereum.svm import NodeFlags
from mythril.laser.smt import simplify

colors = [
    {
        "border": "#26996f",
        "background": "#2f7e5b",
        "highlight": {"border": "#fff", "background": "#28a16f"},
    },
    {
        "border": "#9e42b3",
        "background": "#842899",
        "highlight": {"border": "#fff", "background": "#933da6"},
    },
    {
        "border": "#b82323",
        "background": "#991d1d",
        "highlight": {"border": "#fff", "background": "#a61f1f"},
    },
    {
        "border": "#4753bf",
        "background": "#3b46a1",
        "highlight": {"border": "#fff", "background": "#424db3"},
    },
    {
        "border": "#26996f",
        "background": "#2f7e5b",
        "highlight": {"border": "#fff", "background": "#28a16f"},
    },
    {
        "border": "#9e42b3",
        "background": "#842899",
        "highlight": {"border": "#fff", "background": "#933da6"},
    },
    {
        "border": "#b82323",
        "background": "#991d1d",
        "highlight": {"border": "#fff", "background": "#a61f1f"},
    },
    {
        "border": "#4753bf",
        "background": "#3b46a1",
        "highlight": {"border": "#fff", "background": "#424db3"},
    },
]


'''This Python file is a module designed to convert a state space (a representation of all possible states and transitions in a smart contract's execution) into a set of state nodes and transition edges. These nodes and edges can then be used to visualize the state space, such as in a graph or diagram. '''
def get_serializable_statespace(statespace):
    """

    :param statespace:
    :return:
    """
    nodes = []  # A list to store serialized nodes.
    edges = []  # A list to store serialized edges.

    color_map = {}  # A dictionary to map contract names to color schemes.
    i = 0
    """Assign Colors to Contracts:
    Iterate over the accounts in the state space and assign a unique color scheme to each contract based on its name."""
    for k in statespace.accounts:
        color_map[statespace.accounts[k].contract_name] = colors[i]
        i += 1

    # Process Nodes:
    for node_key in statespace.nodes:
        node = statespace.nodes[node_key]

        # Extract the node's code
        code = node.get_cfg_dict()["code"]
        code = re.sub("([0-9a-f]{8})[0-9a-f]+", lambda m: m.group(1) + "(...)", code)

        #  format it (e.g., truncate long code snippets and replace JUMPDEST with function names).
        if NodeFlags.FUNC_ENTRY in node.flags:
            code = re.sub("JUMPDEST", node.function_name, code)

        code_split = code.split("\\n")

        truncated_code = (
            code
            if (len(code_split) < 7)
            else "\\n".join(code_split[:6]) + "\\n(click to expand +)"
        )

        # Determine the color for the node based on its contract name.
        try:
            color = color_map[node.get_cfg_dict()["contract_name"]]
        except KeyError:
            color = colors[i]
            i += 1
            color_map[node.get_cfg_dict()["contract_name"]] = color

        """Extract the state information for the node, including:
        The machine state (e.g., stack, memory, program counter).
        Account information (e.g., balances, storage)."""
        def get_state_accounts(node_state):
            """

            :param node_state:
            :return:
            """
            state_accounts = []
            for key in node_state.accounts:
                account = node_state.accounts[key].as_dict
                account.pop("code", None)
                account["balance"] = str(account["balance"])

                storage = {}
                for storage_key in account["storage"].printable_storage:
                    storage[str(storage_key)] = str(account["storage"][storage_key])

                state_accounts.append({"address": key, "storage": storage})
            return state_accounts

        states = [
            {"machine": x.mstate.as_dict, "accounts": get_state_accounts(x)}
            for x in node.states
        ]

        for state in states:
            state["machine"]["stack"] = [str(s) for s in state["machine"]["stack"]]
            state["machine"]["memory"] = [
                str(m)
                for m in state["machine"]["memory"][: len(state["machine"]["memory"])]
            ]

        truncated_code = truncated_code.replace("\\n", "\n")
        code = code.replace("\\n", "\n")

        """Create a serialized node object (s_node) containing:
        id: A unique identifier for the node.
        func: The function name associated with the node.
        label: A truncated version of the code for display purposes.
        code: The full code associated with the node.
        truncated: The truncated code.
        states: The machine and account states.
        color: The color scheme for the node.
        instructions: The code split into individual instructions."""
        s_node = {
            "id": str(node_key),
            "func": str(node.function_name),
            "label": truncated_code,
            "code": code,
            "truncated": truncated_code,
            "states": states,
            "color": color,
            "instructions": code.split("\n"),
        }

        # Add the serialized node to the nodes list.
        nodes.append(s_node)

    for edge in statespace.edges:
        if edge.condition is None:
            label = ""
        else:
            try:
                label = str(simplify(edge.condition)).replace("\n", "")
            except Z3Exception:
                label = str(edge.condition).replace("\n", "")

        label = re.sub(
            "([^_])([\d]{2}\d+)", lambda m: m.group(1) + hex(int(m.group(2))), label
        )

        s_edge = {
            "from": str(edge.as_dict["from"]),
            "to": str(edge.as_dict["to"]),
            "arrows": "to",
            "label": label,
            "smooth": {"type": "cubicBezier"},
        }

        edges.append(s_edge)

    return {"edges": edges, "nodes": nodes}


'''
Key Concepts:

State Space:
Represents all possible states and transitions in a smart contract's execution.
Includes nodes (states) and edges (transitions between states).

Serialization:
Converts the state space into a format that can be easily stored, transmitted, or visualized.

Visualization:
The serialized output can be used to generate graphs or diagrams, where:
Nodes represent states (e.g., program counter, stack, memory).
Edges represent transitions between states (e.g., conditional jumps).

Color Mapping:
Each contract is assigned a unique color scheme to differentiate it in visualizations.
'''