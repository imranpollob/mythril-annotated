from time import time

from mythril.support.support_utils import Singleton

'''Maintains the start time of the current contract in execution'''
class StartTime(metaclass=Singleton):

    def __init__(self):
        self.global_start_time = time()
