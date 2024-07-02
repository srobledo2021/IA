# search.py
# ---------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


"""
In search.py, you will implement generic search algorithms which are called by
Pacman agents (in searchAgents.py).
"""

import util

class SearchProblem:
    """
    This class outlines the structure of a search problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the search problem.
        """
        util.raiseNotDefined()

    def isGoalState(self, state):
        """
          state: Search state

        Returns True if and only if the state is a valid goal state.
        """
        util.raiseNotDefined()

    def getSuccessors(self, state):
        """
          state: Search state

        For a given state, this should return a list of triples, (successor,
        action, stepCost), where 'successor' is a successor to the current
        state, 'action' is the action required to get there, and 'stepCost' is
        the incremental cost of expanding to that successor.
        """
        util.raiseNotDefined()

    def getCostOfActions(self, actions):
        """
         actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.
        The sequence must be composed of legal moves.
        """
        util.raiseNotDefined()


def tinyMazeSearch(problem):
    """
    Returns a sequence of moves that solves tinyMaze.  For any other maze, the
    sequence of moves will be incorrect, so only use this for tinyMaze.
    """
    from game import Directions
    s = Directions.SOUTH
    w = Directions.WEST
    return  [s, s, w, s, w, w, s, w]

def depthFirstSearch(problem: SearchProblem):
    """
    Search the deepest nodes in the search tree first.

    Your search algorithm needs to return a list of actions that reaches the
    goal. Make sure to implement a graph search algorithm.

    To get started, you might want to try some of these simple commands to
    understand the search problem that is being passed in:
    """
    
    #define a new stack
    state_stack = util.Stack()
    #initialize the stack with initial position
    state_stack.push((problem.getStartState(), []))
    visited = set()

    while not state_stack.isEmpty():
        current, path = state_stack.pop()
        if problem.isGoalState(current):
            return path

        if current not in visited:
            visited.add(current)
            for successor in problem.getSuccessors(current):
                state_stack.push((successor[0], path + [successor[1]]))

    return []


def breadthFirstSearch(problem: SearchProblem):
    """Search the shallowest nodes in the search tree first."""
    # define a queue for open list
    state_queue = util.Queue()
    # initialize open stack with start position
    state_queue.push((problem.getStartState(), []))
    visited_list = []

    while not state_queue.isEmpty():
        current, path = state_queue.pop()
        if current not in visited_list:
            visited_list.append(current)
            if problem.isGoalState(current):
                return path
            else:
                # generate successors of current node
                    successors_of_current = problem.getSuccessors(current)

                    for successor in successors_of_current:
                            state_queue.push((successor[0], path + [successor[1]]))
    return []
    

def uniformCostSearch(problem: SearchProblem):
    """Search the node of least total cost first."""
    #queue to keep states
    state_queue = util.PriorityQueue()
    # initialize open stack with start position
    state_queue.push((problem.getStartState(),[],0),0)
    visited = set()

    while not state_queue.isEmpty():
        current, path, cost = state_queue.pop()
        if problem.isGoalState(current):
            return path

        if current not in visited:
            visited.add(current)
            for successor in problem.getSuccessors(current):
                state_queue.push((successor[0], path + [successor[1]], successor[2] + cost),successor[2] + cost)

    return []

def nullHeuristic(state, problem=None):
    """
    A heuristic function estimates the cost from the current state to the nearest
    goal in the provided SearchProblem.  This heuristic is trivial.
    """
    return 0

def aStarSearch(problem: SearchProblem, heuristic=nullHeuristic):
    """Search the node that has the lowest combined cost and heuristic first."""
    #queue to keep states
    state_queue = util.PriorityQueue()
    # initialize open stack with start position
    state_queue.push((problem.getStartState(), [], 0), 0)
    visited_set = []
    closed_list = []
    while not state_queue.isEmpty():
        current, path, cost = state_queue.pop()
        visited_set.append(current)
        if problem.isGoalState(current):
            return path
        else:
            # generate successors of current
            if (current not in closed_list):
                successors = problem.getSuccessors(current)
                closed_list.append(current)

                for each_successor in successors:
                    if (each_successor[0] in visited_set):
                        pass
                    else:
                        heuristic_value = heuristic(each_successor[0],problem)
                        state_queue.update((each_successor[0], path + [each_successor[1]], each_successor[2] + cost),
                                          each_successor[2] + cost + heuristic_value)
    return []


# Abbreviations
bfs = breadthFirstSearch
dfs = depthFirstSearch
astar = aStarSearch
ucs = uniformCostSearch
