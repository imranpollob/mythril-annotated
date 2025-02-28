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

'''converting the symbolic execution state space into a serializable format that can be used for exploration and visualization. 
It takes the statespace object (which is a representation of the execution paths explored by the symbolic execution engine) and transforms it into a set of nodes and edges, each with specific attributes suitable for representing a graph structure in a user interface or other analytical tools. 
The module focuses on structuring and formatting the data rather than performing new analysis.'''

'''Converts the given statespace into a dictionary containing lists of nodes and edges, all of which are in a serializable format (e.g., ready for conversion to JSON).'''
def get_serializable_statespace(statespace):
    """
    :param statespace:
    :return:
    
    Logic:
    - Initializes empty lists nodes and edges to store the serialized nodes and edges, respectively.
    - Creates a color_map to assign a unique color to each contract in the state space, making it easier to visually distinguish between different contracts in the graph.
    - Iterates through the nodes in the statespace and extracts relevant information from each node, including:
        - The code associated with the node, formatted for display (truncated for brevity).
        - Machine state and account information from the node's states.
        - Visual attributes such as color and label.
    - Creates a dictionary (s_node) to represent the serialized node, containing the extracted information.
    - Appends the serialized node to the nodes list.
    - Iterates through the edges in the statespace and extracts relevant information from each edge, including the source node ID (from), destination node ID (to), and the condition (if any) associated with the edge.
    - Creates a dictionary (s_edge) to represent the serialized edge, containing the extracted information.
    - Appends the serialized edge to the edges list.
    - Returns a dictionary containing the nodes and edges lists.
    - Adds information about the accounts into each states data for displaying in a UI
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


