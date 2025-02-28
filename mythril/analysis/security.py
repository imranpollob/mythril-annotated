"""This module contains functionality for hooking in detection modules and
executing them."""

import logging
from typing import List, Optional

from mythril.analysis.module import ModuleLoader, reset_callback_modules
from mythril.analysis.module.base import EntryPoint
from mythril.analysis.report import Issue

log = logging.getLogger(__name__)

'''It acts as the central coordinator for "firing the lasers" (executing the detection modules) on the symbolic execution state space. The key functions are designed to locate, execute, and gather the issues discovered by these modules. It handles both regular, post-analysis modules and callback-based modules which run during the symbolic execution itself.'''

'''Retrieves the issues reported by callback-style detection modules.'''
def retrieve_callback_issues(white_list: Optional[List[str]] = None) -> List[Issue]:
    issues: List[Issue] = []
    for module in ModuleLoader().get_detection_modules(
        entry_point=EntryPoint.CALLBACK, white_list=white_list
    ):
        log.debug("Retrieving results for " + module.name)
        issues += module.issues

    reset_callback_modules(module_names=white_list)

    return issues


'''Executes the security analysis modules on the symbolic state space and collects the discovered issues.'''
def fire_lasers(statespace, white_list: Optional[List[str]] = None) -> List[Issue]:
    """Fire lasers at analysed statespace object

    :param statespace: Symbolic statespace to analyze
    :param white_list: Optionally whitelist modules to use for the analysis
    :return: Discovered issues
    """
    log.info("Starting analysis")

    issues: List[Issue] = []
    for module in ModuleLoader().get_detection_modules(
        entry_point=EntryPoint.POST, white_list=white_list
    ):
        log.info("Executing " + module.name)
        issues += module.execute(statespace)

    issues += retrieve_callback_issues(white_list)
    return issues
