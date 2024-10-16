# bayesAgents.py
# --------------
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


import bayesNet as bn
import game
from game import Actions, Agent, Directions
import inference
import layout
import factorOperations
import itertools
import operator as op
import random
import functools
import util

from hunters import GHOST_COLLISION_REWARD, WON_GAME_REWARD
from layout import PROB_BOTH_TOP, PROB_BOTH_BOTTOM, PROB_ONLY_LEFT_TOP, \
    PROB_ONLY_LEFT_BOTTOM, PROB_FOOD_RED, PROB_GHOST_RED

X_POS_VAR = "xPos"
FOOD_LEFT_VAL = "foodLeft"
GHOST_LEFT_VAL = "ghostLeft"
X_POS_VALS = [FOOD_LEFT_VAL, GHOST_LEFT_VAL]

Y_POS_VAR = "yPos"
BOTH_TOP_VAL = "bothTop"
BOTH_BOTTOM_VAL = "bothBottom"
LEFT_TOP_VAL = "leftTop"
LEFT_BOTTOM_VAL = "leftBottom"
Y_POS_VALS = [BOTH_TOP_VAL, BOTH_BOTTOM_VAL, LEFT_TOP_VAL, LEFT_BOTTOM_VAL]

FOOD_HOUSE_VAR = "foodHouse"
GHOST_HOUSE_VAR = "ghostHouse"
HOUSE_VARS = [FOOD_HOUSE_VAR, GHOST_HOUSE_VAR]

TOP_LEFT_VAL = "topLeft"
TOP_RIGHT_VAL = "topRight"
BOTTOM_LEFT_VAL = "bottomLeft"
BOTTOM_RIGHT_VAL = "bottomRight"
HOUSE_VALS = [TOP_LEFT_VAL, TOP_RIGHT_VAL, BOTTOM_LEFT_VAL, BOTTOM_RIGHT_VAL]

OBS_VAR_TEMPLATE = "obs(%d,%d)"

BLUE_OBS_VAL = "blue"
RED_OBS_VAL = "red"
NO_OBS_VAL = "none"
OBS_VALS = [BLUE_OBS_VAL, RED_OBS_VAL, NO_OBS_VAL]

ENTER_LEFT = 0
ENTER_RIGHT = 1
EXPLORE = 2

def constructHeartAttackBayesNet():
    """
    Exploring Bayes net functions, printing, and creation.
    Pay close attention to how factors are created and modified.
    """

    # This is the example V structured Bayes' net from the lecture 
    # on Bayes' nets independence.
    # Constructing Bayes' nets: variables list
    variableList = ['Exercise', 'BP', 'Smokes', 'Chol', 'Attack']

    # Constructing Bayes' nets, edge list: (x, y) means edge from x to y
    edgeTuplesList = [('Exercise', 'BP'), ('Smokes', 'BP'), ('Smokes','Chol'), ('BP', 'Attack')]

    # Construct the domain for each variable (a list like)
    variableDomainsDict = {}
    variableDomainsDict['Exercise']  = ['true', 'false']
    variableDomainsDict['BP'] = ['true', 'false']
    variableDomainsDict['Smokes']  = ['true', 'false']
    variableDomainsDict['Chol']  = ['true', 'false']
    variableDomainsDict['Attack']  = ['true', 'false']

    # None of the conditional probability tables are assigned yet in our Bayes' net
    bayesNet = bn.constructEmptyBayesNet(variableList, edgeTuplesList, variableDomainsDict)

    # Create a factor for each CPT.  
    # The first input is the list of unconditioned variables in your factor,
    # the second input is the list of conditioned variables in your factor,
    # and the third input is the dict of domains for your variables.
    exerciseCPT  = bn.Factor(['Exercise'], [], variableDomainsDict)

    # We use assignmentDicts to set and get probability entries from Factors.
    # An assignmentDict is a dict {variable : variableValue} of assignments 
    # of variables to values (where the variableValue must be in 
    # variableDomainsDict[variable]

    exerciseAssignmentDict = {'Exercise' : 'true'}
    exerciseCPT.setProbability(exerciseAssignmentDict, 0.4)

    exerciseAssignmentDict = {'Exercise' : 'false'}
    exerciseCPT.setProbability(exerciseAssignmentDict, 0.6)

    print(exerciseCPT)

    # The traffic factor has two conditioned variables and one unconditioned 
    # variable.  Each variable has a domain size of 2, so we have 
    # 2^3 = 8 possible assignments (and thus 8 rows in our probability table).

    BPCPT  = bn.Factor(['BP'], ['Exercise', 'Smokes'], variableDomainsDict)

    BES = {'BP' : 'true', 'Exercise' : 'true', 'Smokes' : 'true'}
    bES = {'BP' : 'false',  'Exercise' : 'true', 'Smokes' : 'true'}    
    BEs = {'BP' : 'true', 'Exercise' : 'true', 'Smokes' : 'false' }
    bEs = {'BP' : 'false',  'Exercise' : 'true', 'Smokes' : 'false' }
    BeS = {'BP' : 'true', 'Exercise' : 'false',  'Smokes' : 'true'}
    beS = {'BP' : 'false',  'Exercise' : 'false',  'Smokes' : 'true'}
    Bes = {'BP' : 'true', 'Exercise' : 'false',  'Smokes' : 'false' }
    bes = {'BP' : 'false',  'Exercise' : 'false',  'Smokes' : 'false' }

    # For a CPT, we must have that the sum of the probability of all the 
    # unconditionedVariables for a given assignment of conditioned 
    # variables must sum to 1
    BPCPT.setProbability(BES, 0.45)
    BPCPT.setProbability(bES, 0.55)
    BPCPT.setProbability(BEs, 0.05)
    BPCPT.setProbability(bEs, 0.95)
    BPCPT.setProbability(BeS, 0.95)
    BPCPT.setProbability(beS, 0.05)
    BPCPT.setProbability(Bes, 0.55)
    BPCPT.setProbability(bes, 0.45)

    print(BPCPT)

    print("You can use factor.getAllPossibleAssignmentDicts() " + \
          "to iterate through all combinations of assignments:\n")
    for assignmentDict in BPCPT.getAllPossibleAssignmentDicts():
        print(assignmentDict)

    # Fill in the ballGame CPT, very similar to raining

    smokesCPT = bn.Factor(['Smokes'], [], variableDomainsDict)

    exerciseAssignmentDict = {'Smokes' : 'true'}
    smokesCPT.setProbability(exerciseAssignmentDict, 0.15)

    exerciseAssignmentDict = {'Smokes' : 'false'}
    smokesCPT.setProbability(exerciseAssignmentDict, 0.85)

    # Note that we can use assignmentDicts that contain assignments for 
    # more variables than a factor mentions.
    # Here, we pass in an assignmentDict that has 3 variable assignments 
    # buSmokesCPTesCPT.setProbability(smokesAssignmentDict, 0.85)

    print(smokesCPT)

    AttackCPT  = bn.Factor(['Attack'], ['BP'], variableDomainsDict)

    AB = {'Attack' : 'true', 'BP' : 'true'}
    aB = {'Attack' : 'false',  'BP' : 'true'}    
    Ab = {'Attack' : 'true', 'BP' : 'false'}
    ab = {'Attack' : 'false',  'BP' : 'false'}

    # For a CPT, we must have that the sum of the probability of all the 
    # unconditionedVariables for a given assignment of conditioned 
    # variables must sum to 1
    AttackCPT.setProbability(AB, 0.75)
    AttackCPT.setProbability(aB, 0.25)
    AttackCPT.setProbability(Ab, 0.05)
    AttackCPT.setProbability(ab, 0.95)

    print(AttackCPT)

    for assignmentDict in AttackCPT.getAllPossibleAssignmentDicts():
        print(assignmentDict)


    CholCPT  = bn.Factor(['Chol'], ['Smokes'], variableDomainsDict)

    CS = {'Chol' : 'true', 'Smokes' : 'true'}
    cS = {'Chol' : 'false',  'Smokes' : 'true'}    
    Cs = {'Chol' : 'true', 'Smokes' : 'false'}
    cs = {'Chol' : 'false',  'Smokes' : 'false'}

    # For a CPT, we must have that the sum of the probability of all the 
    # unconditionedVariables for a given assignment of conditioned 
    # variables must sum to 1
    CholCPT.setProbability(CS, 0.8)
    CholCPT.setProbability(cS, 0.2)
    CholCPT.setProbability(Cs, 0.4)
    CholCPT.setProbability(cs, 0.6)

    print(CholCPT)

    for assignmentDict in CholCPT.getAllPossibleAssignmentDicts():
        print(assignmentDict)



    # Set the factors for the bayes net to be these CPTs
    bayesNet.setCPT('Exercise',  exerciseCPT)
    bayesNet.setCPT('BP', BPCPT)
    bayesNet.setCPT('Smokes',  smokesCPT)
    bayesNet.setCPT('Chol',  CholCPT)
    bayesNet.setCPT('Attack', AttackCPT)

    print(bayesNet)

    print(bayesNet.easierToParseString())

    return(bayesNet)

def constructBayesNet(gameState):
    """
    Question 1: Bayes net structure

    Construct an empty Bayes net according to the structure given in the project
    description.

    There are 5 kinds of variables in this Bayes net:
    - a single "x position" variable (controlling the x pos of the houses)
    - a single "y position" variable (controlling the y pos of the houses)
    - a single "food house" variable (containing the house centers)
    - a single "ghost house" variable (containing the house centers)
    - a large number of "observation" variables for each cell Pacman can measure

    You *must* name all position and house variables using the constants
    (X_POS_VAR, FOOD_HOUSE_VAR, etc.) at the top of this file. 

    The full set of observation variables can be obtained as follows:

        for housePos in gameState.getPossibleHouses():
            for obsPos in gameState.getHouseWalls(housePos)
                obsVar = OBS_VAR_TEMPLATE % obsPos

    In this method, you should:
    - populate `obsVars` using the procedure above
    - populate `edges` with every edge in the Bayes Net (a tuple `(from, to)`)
    - set each `variableDomainsDict[var] = values`, where `values` is the set
      of possible assignments to `var`. These should again be set using the
      constants defined at the top of this file.
    """

    obsVars = []
    edges = []
    variableDomainsDict = {}

    "*** YOUR CODE HERE ***"
    #obsVars es l observacion actual
    for housePos in gameState.getPossibleHouses():
            for obsPos in gameState.getHouseWalls(housePos):
                obsVar = OBS_VAR_TEMPLATE % obsPos
                obsVars.append(obsVar)
                edges.append((FOOD_HOUSE_VAR, obsVar))
                edges.append((GHOST_HOUSE_VAR, obsVar))
                variableDomainsDict[obsVar] = OBS_VALS
    edges.append((X_POS_VAR, FOOD_HOUSE_VAR))
    edges.append((Y_POS_VAR, FOOD_HOUSE_VAR))
    edges.append((X_POS_VAR, GHOST_HOUSE_VAR))
    edges.append((Y_POS_VAR, GHOST_HOUSE_VAR))
    
    variableDomainsDict[X_POS_VAR] = X_POS_VALS
    variableDomainsDict[Y_POS_VAR] = Y_POS_VALS
    variableDomainsDict[FOOD_HOUSE_VAR] = HOUSE_VALS
    variableDomainsDict[GHOST_HOUSE_VAR] = HOUSE_VALS
 
    "*** END YOUR CODE HERE ***"

    variables = [X_POS_VAR, Y_POS_VAR] + HOUSE_VARS + obsVars
    net = bn.constructEmptyBayesNet(variables, edges, variableDomainsDict)
    return net, obsVars

def fillCPTs(bayesNet, gameState):
    fillXCPT(bayesNet, gameState)
    fillYCPT(bayesNet, gameState)
    fillHouseCPT(bayesNet, gameState)
    fillObsCPT(bayesNet, gameState)

def fillXCPT(bayesNet, gameState):
    from layout import PROB_FOOD_LEFT 
    xFactor = bn.Factor([X_POS_VAR], [], bayesNet.variableDomainsDict())
    xFactor.setProbability({X_POS_VAR: FOOD_LEFT_VAL}, PROB_FOOD_LEFT)
    xFactor.setProbability({X_POS_VAR: GHOST_LEFT_VAL}, 1 - PROB_FOOD_LEFT)
    bayesNet.setCPT(X_POS_VAR, xFactor)

def fillYCPT(bayesNet, gameState):
    """
    Question 2: Bayes net probabilities

    Fill the CPT that gives the prior probability over the y position variable.
    See the definition of `fillXCPT` above for an example of how to do this.
    You can use the PROB_* constants imported from layout rather than writing
    probabilities down by hand.
    """

    yFactor = bn.Factor([Y_POS_VAR], [], bayesNet.variableDomainsDict())
    "*** YOUR CODE HERE ***"
    yFactor.setProbability({Y_POS_VAR: BOTH_TOP_VAL}, PROB_BOTH_TOP)
    yFactor.setProbability({Y_POS_VAR: BOTH_BOTTOM_VAL}, PROB_BOTH_BOTTOM)
    yFactor.setProbability({Y_POS_VAR: LEFT_TOP_VAL}, PROB_ONLY_LEFT_TOP)
    yFactor.setProbability({Y_POS_VAR: LEFT_BOTTOM_VAL}, PROB_ONLY_LEFT_BOTTOM)
    "*** END YOUR CODE HERE ***"
    bayesNet.setCPT(Y_POS_VAR, yFactor)

def fillHouseCPT(bayesNet, gameState):
    foodHouseFactor = bn.Factor([FOOD_HOUSE_VAR], [X_POS_VAR, Y_POS_VAR], bayesNet.variableDomainsDict())
    for assignment in foodHouseFactor.getAllPossibleAssignmentDicts():
        left = assignment[X_POS_VAR] == FOOD_LEFT_VAL
        top = assignment[Y_POS_VAR] == BOTH_TOP_VAL or \
                (left and assignment[Y_POS_VAR] == LEFT_TOP_VAL)

        if top and left and assignment[FOOD_HOUSE_VAR] == TOP_LEFT_VAL or \
                top and not left and assignment[FOOD_HOUSE_VAR] == TOP_RIGHT_VAL or \
                not top and left and assignment[FOOD_HOUSE_VAR] == BOTTOM_LEFT_VAL or \
                not top and not left and assignment[FOOD_HOUSE_VAR] == BOTTOM_RIGHT_VAL:
            prob = 1
        else:
            prob = 0

        foodHouseFactor.setProbability(assignment, prob)
    bayesNet.setCPT(FOOD_HOUSE_VAR, foodHouseFactor)

    ghostHouseFactor = bn.Factor([GHOST_HOUSE_VAR], [X_POS_VAR, Y_POS_VAR], bayesNet.variableDomainsDict())
    for assignment in ghostHouseFactor.getAllPossibleAssignmentDicts():
        left = assignment[X_POS_VAR] == GHOST_LEFT_VAL
        top = assignment[Y_POS_VAR] == BOTH_TOP_VAL or \
                (left and assignment[Y_POS_VAR] == LEFT_TOP_VAL)

        if top and left and assignment[GHOST_HOUSE_VAR] == TOP_LEFT_VAL or \
                top and not left and assignment[GHOST_HOUSE_VAR] == TOP_RIGHT_VAL or \
                not top and left and assignment[GHOST_HOUSE_VAR] == BOTTOM_LEFT_VAL or \
                not top and not left and assignment[GHOST_HOUSE_VAR] == BOTTOM_RIGHT_VAL:
            prob = 1
        else:
            prob = 0

        ghostHouseFactor.setProbability(assignment, prob)
    bayesNet.setCPT(GHOST_HOUSE_VAR, ghostHouseFactor)

def fillObsCPT(bayesNet, gameState):
    """
    This funcion fills the CPT that gives the probability of an observation in each square,
    given the locations of the food and ghost houses.

    This function creates a new factor for *each* of 4*7 = 28 observation
    variables. Don't forget to call bayesNet.setCPT for each factor you create.

    The XXXPos variables at the beginning of this method contain the (x, y)
    coordinates of each possible house location.

    IMPORTANT:
    Because of the particular choice of probabilities higher up in the Bayes
    net, it will never be the case that the ghost house and the food house are
    in the same place. However, the CPT for observations must still include a
    vaild probability distribution for this case. To conform with the
    autograder, this function uses the *food house distribution* over colors when both the food
    house and ghost house are assigned to the same cell.
    """

    bottomLeftPos, topLeftPos, bottomRightPos, topRightPos = gameState.getPossibleHouses()

    #convert coordinates to values (strings)
    coordToString = {
        bottomLeftPos: BOTTOM_LEFT_VAL,
        topLeftPos: TOP_LEFT_VAL,
        bottomRightPos: BOTTOM_RIGHT_VAL,
        topRightPos: TOP_RIGHT_VAL
    }

    for housePos in gameState.getPossibleHouses():
        for obsPos in gameState.getHouseWalls(housePos):

            obsVar = OBS_VAR_TEMPLATE % obsPos
            newObsFactor = bn.Factor([obsVar], [GHOST_HOUSE_VAR, FOOD_HOUSE_VAR], bayesNet.variableDomainsDict())
            assignments = newObsFactor.getAllPossibleAssignmentDicts()

            for assignment in assignments:
                houseVal = coordToString[housePos]
                ghostHouseVal = assignment[GHOST_HOUSE_VAR]
                foodHouseVal = assignment[FOOD_HOUSE_VAR]

                if houseVal != ghostHouseVal and houseVal != foodHouseVal:
                    newObsFactor.setProbability({
                        obsVar: RED_OBS_VAL,
                        GHOST_HOUSE_VAR: ghostHouseVal,
                        FOOD_HOUSE_VAR: foodHouseVal}, 0)
                    newObsFactor.setProbability({
                        obsVar: BLUE_OBS_VAL,
                        GHOST_HOUSE_VAR: ghostHouseVal,
                        FOOD_HOUSE_VAR: foodHouseVal}, 0)
                    newObsFactor.setProbability({
                        obsVar: NO_OBS_VAL,
                        GHOST_HOUSE_VAR: ghostHouseVal,
                        FOOD_HOUSE_VAR: foodHouseVal}, 1)
                else:
                    if houseVal == ghostHouseVal and houseVal == foodHouseVal:
                        prob_red = PROB_FOOD_RED
                    elif houseVal == ghostHouseVal:
                        prob_red = PROB_GHOST_RED
                    elif houseVal == foodHouseVal:
                        prob_red = PROB_FOOD_RED

                    prob_blue = 1 - prob_red

                    newObsFactor.setProbability({
                        obsVar: RED_OBS_VAL,
                        GHOST_HOUSE_VAR: ghostHouseVal,
                        FOOD_HOUSE_VAR: foodHouseVal}, prob_red)
                    newObsFactor.setProbability({
                        obsVar: BLUE_OBS_VAL,
                        GHOST_HOUSE_VAR: ghostHouseVal,
                        FOOD_HOUSE_VAR: foodHouseVal}, prob_blue)
                    newObsFactor.setProbability({
                        obsVar: NO_OBS_VAL,
                        GHOST_HOUSE_VAR: ghostHouseVal,
                        FOOD_HOUSE_VAR: foodHouseVal}, 0)

            bayesNet.setCPT(obsVar, newObsFactor)

def getMostLikelyFoodHousePosition(evidence, bayesNet, eliminationOrder):
    """
    Question 7: Marginal inference for pacman

    Find the most probable position for the food house.
    First, call the variable elimination method you just implemented to obtain
    p(FoodHouse | everything else). Then, inspect the resulting probability
    distribution to find the most probable location of the food house. Return
    this.

    (This should be a very short method.)
    """
    "*** YOUR CODE HERE ***"
    #obtain p(FoodHouse | everything else)
    factor = inference.inferenceByVariableElimination(bayesNet, ['foodHouse','ghostHouse'], evidence, eliminationOrder)
    max_probability = 0
    assignments = factor.getAllPossibleAssignmentDicts()

    #check for the highest probability among the assignments
    for assignment in assignments:
        assignment_probability = factor.getProbability(assignment)
        if assignment_probability > max_probability:
            best_assignment = assignment
            max_probability = assignment_probability
    return best_assignment
    "*** END YOUR CODE HERE ***"


class BayesAgent(game.Agent):

    def registerInitialState(self, gameState):
        self.bayesNet, self.obsVars = constructBayesNet(gameState)
        fillCPTs(self.bayesNet, gameState)

        self.distances = cacheDistances(gameState)
        self.visited = set()
        self.steps = 0

    def getAction(self, gameState):
        self.visited.add(gameState.getPacmanPosition())
        self.steps += 1

        if self.steps < 40:
            return self.getRandomAction(gameState)
        else:
            return self.goToBest(gameState)

    def getRandomAction(self, gameState):
        legal = list(gameState.getLegalActions())
        legal.remove(Directions.STOP)
        random.shuffle(legal)
        successors = [gameState.generatePacmanSuccessor(a).getPacmanPosition() for a in legal]
        ls = [(a, s) for a, s in zip(legal, successors) if s not in gameState.getPossibleHouses()]
        ls.sort(key=lambda p: p[1] in self.visited)
        return ls[0][0]

    def getEvidence(self, gameState):
        evidence = {}
        for ePos, eColor in gameState.getEvidence().items():
            obsVar = OBS_VAR_TEMPLATE % ePos
            obsVal = {
                "B": BLUE_OBS_VAL,
                "R": RED_OBS_VAL,
                " ": NO_OBS_VAL
            }[eColor]
            evidence[obsVar] = obsVal
        return evidence

    def goToBest(self, gameState):
        evidence = self.getEvidence(gameState)
        unknownVars = [o for o in self.obsVars if o not in evidence]
        eliminationOrder = unknownVars + [X_POS_VAR, Y_POS_VAR, GHOST_HOUSE_VAR]
        bestFoodAssignment = getMostLikelyFoodHousePosition(evidence, 
                self.bayesNet, eliminationOrder)

        tx, ty = dict(
            zip([BOTTOM_LEFT_VAL, TOP_LEFT_VAL, BOTTOM_RIGHT_VAL, TOP_RIGHT_VAL],
                gameState.getPossibleHouses()))[bestFoodAssignment[FOOD_HOUSE_VAR]]
        bestAction = None
        bestDist = float("inf")
        for action in gameState.getLegalActions():
            succ = gameState.generatePacmanSuccessor(action)
            nextPos = succ.getPacmanPosition()
            dist = self.distances[nextPos, (tx, ty)]
            if dist < bestDist:
                bestDist = dist
                bestAction = action
        return bestAction

class VPIAgent(BayesAgent):

    def __init__(self):
        BayesAgent.__init__(self)
        self.behavior = None
        NORTH = Directions.NORTH
        SOUTH = Directions.SOUTH
        EAST = Directions.EAST
        WEST = Directions.WEST
        self.exploreActionsRemaining = \
                list(reversed([NORTH, NORTH, NORTH, NORTH, EAST, EAST, EAST,
                    EAST, SOUTH, SOUTH, SOUTH, SOUTH, WEST, WEST, WEST, WEST]))

    def reveal(self, gameState):
        bottomLeftPos, topLeftPos, bottomRightPos, topRightPos = \
                gameState.getPossibleHouses()
        for housePos in [bottomLeftPos, topLeftPos, bottomRightPos]:
            for ox, oy in gameState.getHouseWalls(housePos):
                gameState.data.observedPositions[ox][oy] = True

    def computeEnterValues(self, evidence, eliminationOrder):
        """
        Question 8a: Value of perfect information

        Given the evidence, compute the value of entering the left and right
        houses immediately. You can do this by obtaining the joint distribution
        over the food and ghost house positions using your inference procedure.
        The reward associated with entering each house is given in the *_REWARD
        variables at the top of the file.

        *Do not* take into account the "time elapsed" cost of traveling to each
        of the houses---this is calculated elsewhere in the code.
        """

        leftExpectedValue = 0
        rightExpectedValue = 0

        "*** YOUR CODE HERE ***"
        util.raiseNotDefined()
        "*** END YOUR CODE HERE ***"

        return leftExpectedValue, rightExpectedValue

    def getExplorationProbsAndOutcomes(self, evidence):
        unknownVars = [o for o in self.obsVars if o not in evidence]
        assert len(unknownVars) == 7
        assert len(set(evidence.keys()) & set(unknownVars)) == 0
        firstUnk = unknownVars[0]
        restUnk = unknownVars[1:]

        unknownVars = [o for o in self.obsVars if o not in evidence]
        eliminationOrder = unknownVars + [X_POS_VAR, Y_POS_VAR]
        houseMarginals = inference.inferenceByVariableElimination(self.bayesNet,
                [FOOD_HOUSE_VAR, GHOST_HOUSE_VAR], evidence, eliminationOrder)

        probs = [0 for i in range(8)]
        outcomes = []
        for nRed in range(8):
            outcomeVals = [RED_OBS_VAL] * nRed + [BLUE_OBS_VAL] * (7 - nRed)
            outcomeEvidence = dict(zip(unknownVars, outcomeVals))
            outcomeEvidence.update(evidence)
            outcomes.append(outcomeEvidence)

        for foodHouseVal, ghostHouseVal in [(TOP_LEFT_VAL, TOP_RIGHT_VAL),
                (TOP_RIGHT_VAL, TOP_LEFT_VAL)]:

            condEvidence = dict(evidence)
            condEvidence.update({FOOD_HOUSE_VAR: foodHouseVal, 
                GHOST_HOUSE_VAR: ghostHouseVal})
            assignmentProb = houseMarginals.getProbability(condEvidence)

            oneObsMarginal = inference.inferenceByVariableElimination(self.bayesNet,
                    [firstUnk], condEvidence, restUnk + [X_POS_VAR, Y_POS_VAR])

            assignment = oneObsMarginal.getAllPossibleAssignmentDicts()[0]
            assignment[firstUnk] = RED_OBS_VAL
            redProb = oneObsMarginal.getProbability(assignment)

            for nRed in range(8):
                outcomeProb = combinations(7, nRed) * \
                        redProb ** nRed * (1 - redProb) ** (7 - nRed)
                outcomeProb *= assignmentProb
                probs[nRed] += outcomeProb

        return list(zip(probs, outcomes))

    def computeExploreValue(self, evidence, enterEliminationOrder):
        """
        Question 8b: Value of perfect information

        Compute the expected value of first exploring the remaining unseen
        house, and then entering the house with highest expected value.

        The method `getExplorationProbsAndOutcomes` returns pairs of the form
        (prob, explorationEvidence), where `evidence` is a new evidence
        dictionary with all of the missing observations filled in, and `prob` is
        the probability of that set of observations occurring.

        You can use getExplorationProbsAndOutcomes to
        determine the expected value of acting with this extra evidence.
        """

        expectedValue = 0

        "*** YOUR CODE HERE ***"
        util.raiseNotDefined()
        "*** END YOUR CODE HERE ***"

        return expectedValue

    def getAction(self, gameState):

        if self.behavior == None:
            self.reveal(gameState)
            evidence = self.getEvidence(gameState)
            unknownVars = [o for o in self.obsVars if o not in evidence]
            enterEliminationOrder = unknownVars + [X_POS_VAR, Y_POS_VAR]
            exploreEliminationOrder = [X_POS_VAR, Y_POS_VAR]

            print(evidence)
            print(enterEliminationOrder)
            print(exploreEliminationOrder)
            enterLeftValue, enterRightValue = \
                    self.computeEnterValues(evidence, enterEliminationOrder)
            exploreValue = self.computeExploreValue(evidence,
                    exploreEliminationOrder)

            # TODO double-check
            enterLeftValue -= 4
            enterRightValue -= 4
            exploreValue -= 20

            bestValue = max(enterLeftValue, enterRightValue, exploreValue)
            if bestValue == enterLeftValue:
                self.behavior = ENTER_LEFT
            elif bestValue == enterRightValue:
                self.behavior = ENTER_RIGHT
            else:
                self.behavior = EXPLORE

            # pause 1 turn to reveal the visible parts of the map
            return Directions.STOP

        if self.behavior == ENTER_LEFT:
            return self.enterAction(gameState, left=True)
        elif self.behavior == ENTER_RIGHT:
            return self.enterAction(gameState, left=False)
        else:
            return self.exploreAction(gameState)

    def enterAction(self, gameState, left=True):
        bottomLeftPos, topLeftPos, bottomRightPos, topRightPos = \
                gameState.getPossibleHouses()

        dest = topLeftPos if left else topRightPos

        actions = gameState.getLegalActions()
        neighbors = [gameState.generatePacmanSuccessor(a) for a in actions]
        neighborStates = [s.getPacmanPosition() for s in neighbors]
        best = min(zip(actions, neighborStates), 
                key=lambda x: self.distances[x[1], dest])
        return best[0]

    def exploreAction(self, gameState):
        if self.exploreActionsRemaining:
            return self.exploreActionsRemaining.pop()

        evidence = self.getEvidence(gameState)
        enterLeftValue, enterRightValue = self.computeEnterValues(evidence,
                [X_POS_VAR, Y_POS_VAR])

        if enterLeftValue > enterRightValue:
            self.behavior = ENTER_LEFT
            return self.enterAction(gameState, left=True)
        else:
            self.behavior = ENTER_RIGHT
            return self.enterAction(gameState, left=False)

def cacheDistances(state):
    width, height = state.data.layout.width, state.data.layout.height
    states = [(x, y) for x in range(width) for y in range(height)]
    walls = state.getWalls().asList() + state.data.layout.redWalls.asList() + state.data.layout.blueWalls.asList()
    states = [s for s in states if s not in walls]
    distances = {}
    for i in states:
        for j in states:
            if i == j:
                distances[i, j] = 0
            elif util.manhattanDistance(i, j) == 1:
                distances[i, j] = 1
            else:
                distances[i, j] = 999999
    for k in states:
        for i in states:
            for j in states:
                if distances[i,j] > distances[i,k] + distances[k,j]:
                    distances[i,j] = distances[i,k] + distances[k,j]

    return distances

# http://stackoverflow.com/questions/4941753/is-there-a-math-ncr-function-in-python
def combinations(n, r):
    r = min(r, n-r)
    if r == 0: return 1
    numer = functools.reduce(op.mul, range(n, n-r, -1))
    denom = functools.reduce(op.mul, range(1, r+1))
    return numer / denom
