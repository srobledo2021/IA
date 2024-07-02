# logicPlan.py
# ------------
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
In logicPlan.py, you will implement logic planning methods which are called by
Pacman agents (in logicAgents.py).
"""

from typing import Dict, List, Tuple, Callable, Generator, Any
import util
import sys
import logic
import game

from logic import conjoin, disjoin
from logic import PropSymbolExpr, Expr, to_cnf, pycoSAT, parseExpr, pl_true

import itertools
import copy

pacman_str = 'P'
food_str = 'FOOD'
wall_str = 'WALL'
pacman_wall_str = pacman_str + wall_str
ghost_pos_str = 'G'
ghost_east_str = 'GE'
pacman_alive_str = 'PA'
DIRECTIONS = ['North', 'South', 'East', 'West']
blocked_str_map = dict([(direction, (direction + "_blocked").upper()) for direction in DIRECTIONS])
geq_num_adj_wall_str_map = dict([(num, "GEQ_{}_adj_walls".format(num)) for num in range(1, 4)])
DIR_TO_DXDY_MAP = {'North':(0, 1), 'South':(0, -1), 'East':(1, 0), 'West':(-1, 0)}


#______________________________________________________________________________
# QUESTION 1

def sentence1() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    A or B
    (not A) if and only if ((not B) or C)
    (not A) or (not B) or C
    """
    "*** BEGIN YOUR CODE HERE ***"
    a = Expr("A")
    b = Expr("B")
    c = Expr("C")
    first = a | b
    second = ~a % (~b | c)
    third = disjoin(~a, ~b, c)
    return conjoin(first, second, third)
    "*** END YOUR CODE HERE ***"


def sentence2() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """

    "*** BEGIN YOUR CODE HERE ***"
    a = Expr("A")
    b = Expr("B")
    c = Expr("C")
    d = Expr("D")
    first = c % (b | d)
    second = a >> (~b & ~d)
    third = ~(b & ~c) >> a
    fourth = ~d >> c
    return conjoin(first, second, third, fourth)
    "*** END YOUR CODE HERE ***"


def sentence3() -> Expr:
    """Using the symbols PacmanAlive_1 PacmanAlive_0, PacmanBorn_0, and PacmanKilled_0,
    created using the PropSymbolExpr constructor, return a PropSymbolExpr
    instance that encodes the following English sentences (in this order):

    Pacman is alive at time 1 if and only if Pacman was alive at time 0 and it was
    not killed at time 0 or it was not alive at time 0 and it was born at time 0.

    Pacman cannot both be alive at time 0 and be born at time 0.

    Pacman is born at time 0.
    (Project update: for this question only, [0] and _t are both acceptable.)
    """
    "*** BEGIN YOUR CODE HERE ***"
    PacmanAlive_0 = logic.PropSymbolExpr('PacmanAlive',time=0)
    PacmanAlive_1 = logic.PropSymbolExpr('PacmanAlive',time=1)
    PacmanBorn_0 = logic.PropSymbolExpr('PacmanBorn',time=0)
    PacmanKilled_0 = logic.PropSymbolExpr('PacmanKilled',time=0)

    s1 = PacmanAlive_1 % (( PacmanAlive_0 & ~PacmanKilled_0) | (~PacmanAlive_0 & PacmanBorn_0))
    s2 = ~(PacmanAlive_0 & PacmanBorn_0)
    s3 = PacmanBorn_0

    return conjoin(s1,s2,s3)
    "*** END YOUR CODE HERE ***"

def findModel(sentence: Expr) -> Dict[Expr, bool]:
    """Given a propositional logic sentence (i.e. a Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    """
    cnf_sentence = to_cnf(sentence)
    return pycoSAT(cnf_sentence)

def findModelCheck() -> Dict[Any, bool]:
    """Returns the result of findModel(Expr('a')) if lower cased expressions were allowed.
    You should not use findModel or Expr in this method.
    This can be solved with a one-line return statement.
    """
    class dummyClass:
        """dummy('A') has representation A, unlike a string 'A' that has repr 'A'.
        Of note: Expr('Name') has representation Name, not 'Name'.
        """
        def __init__(self, variable_name: str = 'A'):
            self.variable_name = variable_name
        
        def __repr__(self):
            return self.variable_name

    return {dummyClass('a'): True}


def entails(premise: Expr, conclusion: Expr) -> bool:
    """Returns True if the premise entails the conclusion and False otherwise.
    """
    "*** BEGIN YOUR CODE HERE ***"
    sentencia = premise & ~conclusion
    if(findModel(sentencia)==False):
        return True
    else:
        return False
    "*** END YOUR CODE HERE ***"

def plTrueInverse(assignments: Dict[Expr, bool], inverse_statement: Expr) -> bool:
    """Returns True if the (not inverse_statement) is True given assignments and False otherwise.
    pl_true may be useful here; see logic.py for its description.
    """
    "*** BEGIN YOUR CODE HERE ***"
    return pl_true(~inverse_statement,assignments)
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 2

def atLeastOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals (i.e. in the form A or ~A), return a single 
    Expr instance in CNF (conjunctive normal form) that represents the logic 
    that at least one of the literals  ist is true.
    >>> A = PropSymbolExpr('A');
    >>> B = PropSymbolExpr('B');
    >>> symbols = [A, B]
    >>> atleast1 = atLeastOne(symbols)
    >>> model1 = {A:False, B:False}
    >>> print(pl_true(atleast1,model1))
    False
    >>> model2 = {A:False, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    >>> model3 = {A:True, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    """
    "*** BEGIN YOUR CODE HERE ***"
    #or
    return disjoin(literals)
    "*** END YOUR CODE HERE ***"


def atMostOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form) that represents the logic that at most one of 
    the expressions in the list is true.
    itertools.combinations may be useful here.
    """
    "*** BEGIN YOUR CODE HERE ***"
    combinations= itertools.combinations(literals, 2)
    clausula = []
    for element in combinations:
        s = ~element[0] | ~element[1]
        clausula.append(s)
    return conjoin(clausula)
    "*** END YOUR CODE HERE ***"


def exactlyOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form)that represents the logic that exactly one of 
    the expressions in the list is true.
    """
    "*** BEGIN YOUR CODE HERE ***"
    return conjoin(atLeastOne(literals), atMostOne(literals))
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 3

def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]=None) -> Expr:
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    """
    now, last = time, time - 1
    possible_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t
    # the if statements give a small performance boost and are required for q4 and q5 correctness
    if walls_grid[x][y+1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None
    
    "*** BEGIN YOUR CODE HERE ***"
    return PropSymbolExpr(pacman_str, x, y, time=now) % disjoin(possible_causes)
    "*** END YOUR CODE HERE ***"


def SLAMSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]) -> Expr:
    """
    Similar to `pacmanSuccessorStateAxioms` but accounts for illegal actions
    where the pacman might not move timestep to timestep.
    Available actions are ['North', 'East', 'South', 'West']
    """
    now, last = time, time - 1
    moved_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t, assuming moved to having moved
    if walls_grid[x][y+1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not moved_causes:
        return None

    moved_causes_sent: Expr = conjoin([~PropSymbolExpr(pacman_str, x, y, time=last) , ~PropSymbolExpr(wall_str, x, y), disjoin(moved_causes)])

    failed_move_causes: List[Expr] = [] # using merged variables, improves speed significantly
    auxilary_expression_definitions: List[Expr] = []
    for direction in DIRECTIONS:
        dx, dy = DIR_TO_DXDY_MAP[direction]
        wall_dir_clause = PropSymbolExpr(wall_str, x + dx, y + dy) & PropSymbolExpr(direction, time=last)
        wall_dir_combined_literal = PropSymbolExpr(wall_str + direction, x + dx, y + dy, time=last)
        failed_move_causes.append(wall_dir_combined_literal)
        auxilary_expression_definitions.append(wall_dir_combined_literal % wall_dir_clause)

    failed_move_causes_sent: Expr = conjoin([
        PropSymbolExpr(pacman_str, x, y, time=last),
        disjoin(failed_move_causes)])

    return conjoin([PropSymbolExpr(pacman_str, x, y, time=now) % disjoin([moved_causes_sent, failed_move_causes_sent])] + auxilary_expression_definitions)


def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None, sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
    Given:
        t: timestep
        all_coords: list of (x, y) coordinates of the entire problem
        non_outer_wall_coords: list of (x, y) coordinates of the entire problem,
            excluding the outer border (these are the actual squares pacman can
            possibly be in)
        walls_grid: 2D array of either -1/0/1 or T/F. Used only for successorAxioms.
            Do NOT use this when making possible locations for pacman to be in.
        sensorModel(t, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
    Return a logic sentence containing all of the following:
        - for all (x, y) in all_coords:
            If a wall is at (x, y) --> Pacman is not at (x, y)
        - Pacman is at exactly one of the squares at timestep t.
        - Pacman takes exactly one action at timestep t.
        - Results of calling sensorModel(...), unless None.
        - Results of calling successorAxioms(...), describing how Pacman can end in various
            locations on this time step. Consider edge cases. Don't call if None.
    """
    pacphysics_sentences = []

    "*** BEGIN YOUR CODE HERE ***"
    for x, y in all_coords:
        s = PropSymbolExpr(wall_str, x, y) >> ~PropSymbolExpr(pacman_str, x, y, time=t)
        pacphysics_sentences.append(s)
    
    position_sentences = []
    for x, y in non_outer_wall_coords:
        position_sentences.append(PropSymbolExpr(pacman_str, x, y, time=t))
    pacphysics_sentences.append(exactlyOne(position_sentences))

    inp_dir = []
    for dir in DIRECTIONS:
        inp_dir.append(PropSymbolExpr(dir, time=t))
    pacphysics_sentences.append(exactlyOne(inp_dir))

    if sensorModel:
        pacphysics_sentences.append(sensorModel(t,non_outer_wall_coords))

    if successorAxioms and t> 0:
        pacphysics_sentences.append(successorAxioms(t,walls_grid,non_outer_wall_coords))
    
    return conjoin(pacphysics_sentences)
    "*** END YOUR CODE HERE ***"



def checkLocationSatisfiability(x1_y1: Tuple[int, int], x0_y0: Tuple[int, int], action0, action1, problem):
    """
    Given:
        - x1_y1 = (x1, y1), a potential location at time t = 1
        - x0_y0 = (x0, y0), Pacman's location at time t = 0
        - action0 = one of the four items in DIRECTIONS, Pacman's action at time t = 0
        - action1 = to ensure match with autograder solution
        - problem = an instance of logicAgents.LocMapProblem
    Note:
        - there's no sensorModel because we know everything about the world
        - the successorAxioms should be allLegalSuccessorAxioms where needed
    Return:
        - a model where Pacman is at (x1, y1) at time t = 1
        - a model where Pacman is not at (x1, y1) at time t = 1
    """
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))
    KB = []
    x0, y0 = x0_y0
    x1, y1 = x1_y1

    # We know which coords are walls:
    map_sent = [PropSymbolExpr(wall_str, x, y) for x, y in walls_list]
    KB.append(conjoin(map_sent))

    "*** BEGIN YOUR CODE HERE ***"
    # Donde se encuentra el pacman en el instante 1 1 1 
    At_1_1_1 = PropSymbolExpr(pacman_str, x1, y1, time=1)

    #Construccion de la base de conocimineto
    
    #Añadir a la KB: pacphysics_axioms(...) con los timesteps adecuados. No
    #hay sensorModel porque sabemos todo respecto al mundo. Donde es
    #necesario, utiliza allLegalSuccessorAxioms para las transiciones teniendo
    #en cuenta que esto es para las reglas de transmisión regular del Pacman.
    KB.append(pacphysicsAxioms(0,all_coords,non_outer_wall_coords,walls_grid,successorAxioms=allLegalSuccessorAxioms))
    KB.append(pacphysicsAxioms(1,all_coords,non_outer_wall_coords,walls_grid,successorAxioms=allLegalSuccessorAxioms))

    # Añadir a la KB: la posición actual de Pacman (x0, y0).
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))

    # Añadir a la KB: que Pacman toma action0.
    KB.append(PropSymbolExpr(action0, time=0))
    # Añadir a la KB: que Pacman toma action1.
    KB.append(PropSymbolExpr(action1, time=1))

    #Haz una query al solucionador SAT con findModel para los dos modelos descritos
    #anteriormente. Las queries deberían ser diferentes. Se puede revisar entails para
    #recordar cómo son las queries
    model_1 = findModel(conjoin(KB) & At_1_1_1)
    model_2 = findModel(conjoin(KB) &  ~At_1_1_1)

    #Se deberá escribir una función que devuelva una tupla con dos modelos
    #(model1, model2).
    return (model_1, model_2)

    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 4

def positionLogicPlan(problem) -> List:
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    x0, y0 = problem.startState
    xg, yg = problem.goal
    
    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), 
            range(height + 2)))
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]
    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    #añadir al pacman la localización en el instante 0
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))
    #50 pasos de tiempo es el MAX
    for t in range(50):
        #print(t)
        #Pacman solo puede estar en una de las localizaciones en 
        #non_wall_coords(dentro del mapa) en el instante de tiempo 
        inp_wall = []
        for x, y in non_wall_coords:
            inp_wall.append(PropSymbolExpr(pacman_str, x, y, time=t))
        KB.append(exactlyOne(inp_wall))

        #encontrar el modelo donde Pacman esté en una posición y que sea el objetivo
        model = findModel(conjoin(KB) & PropSymbolExpr(pacman_str, xg, yg, time=t))
        if model:
            return extractActionSequence(model, actions)
        
        #tomar una accion por instante de tiempo
        inp_dir = []
        for dir in actions:
            inp_dir.append(PropSymbolExpr(dir, time=t))
        KB.append(exactlyOne(inp_dir))
        #KB.append(exactlyOne([PropSymbolExpr('North',t), PropSymbolExpr('South',t) , PropSymbolExpr('North',t), PropSymbolExpr('East',t), PropSymbolExpr('West',t)]))

        #sucesores en el siguiente momento
        for x, y in non_wall_coords:
            KB.append(pacmanSuccessorAxiomSingle(x, y, t+1, walls_grid))
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 5

def foodLogicPlan(problem) -> List:
    """
    Given an instance of a FoodPlanningProblem, return a list of actions that help Pacman
    eat all of the food.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls.asList()
    (x0, y0), food = problem.start
    food = food.asList()

    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    #comida del estado inicial
    for x, y in food:
        KB.append(PropSymbolExpr(food_str, x, y, time=0))

    #añadir al pacman la localización en el instante 0
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))

    #50 pasos de tiempo es el MAX
    for t in range(50):

        #Pacman solo puede estar en una de las localizaciones en 
        #non_wall_coords(dentro del mapa) en el instante de tiempo 
        inp_wall = []
        for x, y in non_wall_coords:
            inp_wall.append(PropSymbolExpr(pacman_str, x, y, time=t))
        KB.append(exactlyOne(inp_wall))

        #la comida no está en la localización en 
        #el instante de tiempo 
        inp_food = []
        for x, y in food:
            inp_food.append(~PropSymbolExpr(food_str, x, y, time=t))
        food_goal = conjoin(inp_food)

        #encontrar el modelo donde Pacman esté en una posición y que haya comida
        model = findModel(conjoin(KB) & food_goal)
        if model:
            return extractActionSequence(model, actions)

        #tomar una accion por instante de tiempo
        inp_dir = []
        for dir in actions:
            inp_dir.append(PropSymbolExpr(dir, time=t))
        KB.append(exactlyOne(inp_dir))

        #sucesores en el momento siguiente
        for x, y in non_wall_coords:
            KB.append(pacmanSuccessorAxiomSingle(x, y, t+1, walls))

        
        for x, y in food:
            #Está el pacman y hay comida en ese momento
            expr = (PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(food_str, x, y, time=t))
            #no hay comida en el siguiente estado
            expr2 = ~PropSymbolExpr(food_str, x, y, time=t+1)
            #no hay comida en el siguiente estado si ya estoy en la comida o aqui aún no hay comida)
            KB.append(expr2 % expr | ~PropSymbolExpr(food_str, x, y, time=t))
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 6

def localization(problem, agent) -> Generator:
    '''
    problem: a LocalizationProblem instance
    agent: a LocalizationLogicAgent instance
    '''
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    for x, y in all_coords:
        if (x, y) in walls_list:
            #dónde están las paredes
            KB.append(PropSymbolExpr(wall_str, x, y))
        else:
            #dónde NO están las paredes
            KB.append(~PropSymbolExpr(wall_str, x, y))

    for t in range(agent.num_timesteps):

        #Agregar información de PacPhysics, acción y percepción a la KB
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords))
        KB.append(PropSymbolExpr(agent.actions[t], t))
        KB.append(sensorAxioms(t, non_outer_wall_coords))
        
        #obtener percepciones
        KB.append(fourBitPerceptRules(t,agent.getPercepts()))
        
        possible_locations = []
        for x, y in non_outer_wall_coords:
            #-----------------PACMAN---------------------------
            #Está el pacman en ese momento
            res = entails(conjoin(KB), PropSymbolExpr(pacman_str, x, y, time=t))
            #No está el pacman en ese momento
            res2 = entails(conjoin(KB), ~PropSymbolExpr(pacman_str, x, y, time=t))
            #Modelo donde el pacman cumpla las características de la KB
            model = findModel(conjoin(KB) & PropSymbolExpr(pacman_str, x, y, time=t))
            #se incluye si está
            if res:
                KB.append(PropSymbolExpr(pacman_str, x, y, time=t))
            #se incluye si no está
            if res2:
                KB.append(~PropSymbolExpr(pacman_str, x, y, time=t))
            if model:
                possible_locations.append((x, y))

        #cambiar de estado
        agent.moveToNextState(agent.actions[t])
        #add succesor axioms
        KB.append(allLegalSuccessorAxioms(t+1, walls_grid, non_outer_wall_coords))
        "*** END YOUR CODE HERE ***"
        yield possible_locations

#______________________________________________________________________________
# QUESTION 7

def mapping(problem, agent) -> Generator:
    '''
    problem: a MappingProblem instance
    agent: a MappingLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # Pacman knows that the outer border of squares are all walls
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    #añadir al pacman la localización en el instante 0
    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0))
    KB.append(~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))

    for t in range(agent.num_timesteps):
        #Agregar información de PacPhysics, acción y percepción a la KB
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, known_map, sensorAxioms, allLegalSuccessorAxioms))
        KB.append(PropSymbolExpr(agent.actions[t], time=t))
        #obtener percepciones
        KB.append(fourBitPerceptRules(t, agent.getPercepts()))

        for (x, y) in non_outer_wall_coords:
            #-----------------WALLS---------------------------
            #Hay pared en ese momento
            wall = entails(conjoin(KB), PropSymbolExpr(wall_str, x, y))
            #No hay pared en ese momento
            no_wall  = entails(conjoin(KB), ~PropSymbolExpr(wall_str, x, y))
            #si hay pared se agrega a la KB
            if wall:                
                KB.append(PropSymbolExpr(wall_str, x, y))
                known_map[x][y] = 1
            #se incluye a la KB si no hay pared
            if no_wall:
                KB.append(~PropSymbolExpr(wall_str, x, y))
                known_map[x][y] = 0
            #anadir a KB: 1 hay wall, 0 no hay wall
        
        agent.moveToNextState(agent.actions[t])
        "*** END YOUR CODE HERE ***"
        yield known_map

#______________________________________________________________________________
# QUESTION 8

def slam(problem, agent) -> Generator:
    '''
    problem: a SLAMProblem instance
    agent: a SLAMLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # We know that the outer_coords are all walls.
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    #Addinitial location to KB. Update known_map accordingly and add the appropriate expression to KB.
    KB.append(PropSymbolExpr(pacman_str ,pac_x_0, pac_y_0, time=0))
    KB.append(~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
    for t in range(agent.num_timesteps):
        #Agregar información de PacPhysics, acción y percepción a la KB
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, known_map, 
                                   SLAMSensorAxioms, SLAMSuccessorAxioms))
        KB.append(PropSymbolExpr(agent.actions[t], time=t))
        KB.append(numAdjWallsPerceptRules(t, agent.getPercepts()))
        
        possible_locations = []
        for (x, y) in non_outer_wall_coords:
            wall = entails(conjoin(KB), PropSymbolExpr(wall_str, x, y))
            #Demostrar que no hay pared en ese momento
            no_wall = entails(conjoin(KB), ~PropSymbolExpr(wall_str, x, y))
            #si hay pared en ese momento se añade
            if wall:                
                KB.append(PropSymbolExpr(wall_str, x, y))
                known_map[x][y] = 1
            #si no hay pared en ese momento se añade
            if no_wall:
                KB.append(~PropSymbolExpr(wall_str, x, y))
                known_map[x][y] = 0
            #Está el pacman en ese momento
            res = entails(conjoin(KB), PropSymbolExpr(pacman_str, x, y, time=t))
            #No está el pacman en ese momento
            res2 = entails(conjoin(KB), ~PropSymbolExpr(pacman_str, x, y, time=t))
            #Modelo donde el pacman cumpla las características de la KB
            model = findModel(conjoin(KB) & PropSymbolExpr(pacman_str, x, y, time=t))
            #igual que muro pero con pacman
            if res:
                KB.append(PropSymbolExpr(pacman_str, x, y, time=t))
            if res2:
                KB.append(~PropSymbolExpr(pacman_str, x, y, time=t))
            if model:
                possible_locations.append((x,y))
            
        agent.moveToNextState(agent.actions[t])
        "*** END YOUR CODE HERE ***"
        yield (known_map, possible_locations)


# Abbreviations
plp = positionLogicPlan
loc = localization
mp = mapping
flp = foodLogicPlan
# Sometimes the logic module uses pretty deep recursion on long expressions
sys.setrecursionlimit(100000)

#______________________________________________________________________________
# Important expression generating functions, useful to read for understanding of this project.


def sensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (
                PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time = t)
        all_percept_exprs.append(percept_unit_clause % disjoin(percept_exprs))

    return conjoin(all_percept_exprs + combo_var_def_exprs)


def fourBitPerceptRules(t: int, percepts: List) -> Expr:
    """
    Localization and Mapping both use the 4 bit sensor, which tells us True/False whether
    a wall is to pacman's north, south, east, and west.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 4, "Percepts must be a length 4 list."

    percept_unit_clauses = []
    for wall_present, direction in zip(percepts, DIRECTIONS):
        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        if not wall_present:
            percept_unit_clause = ~PropSymbolExpr(blocked_str_map[direction], time=t)
        percept_unit_clauses.append(percept_unit_clause) # The actual sensor readings
    return conjoin(percept_unit_clauses)


def numAdjWallsPerceptRules(t: int, percepts: List) -> Expr:
    """
    SLAM uses a weaker numAdjWallsPerceptRules sensor, which tells us how many walls pacman is adjacent to
    in its four directions.
        000 = 0 adj walls.
        100 = 1 adj wall.
        110 = 2 adj walls.
        111 = 3 adj walls.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 3, "Percepts must be a length 3 list."

    percept_unit_clauses = []
    for i, percept in enumerate(percepts):
        n = i + 1
        percept_literal_n = PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t)
        if not percept:
            percept_literal_n = ~percept_literal_n
        percept_unit_clauses.append(percept_literal_n)
    return conjoin(percept_unit_clauses)


def SLAMSensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        blocked_dir_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        all_percept_exprs.append(blocked_dir_clause % disjoin(percept_exprs))

    percept_to_blocked_sent = []
    for n in range(1, 4):
        wall_combos_size_n = itertools.combinations(blocked_str_map.values(), n)
        n_walls_blocked_sent = disjoin([
            conjoin([PropSymbolExpr(blocked_str, time=t) for blocked_str in wall_combo])
            for wall_combo in wall_combos_size_n])
        # n_walls_blocked_sent is of form: (N & S) | (N & E) | ...
        percept_to_blocked_sent.append(
            PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t) % n_walls_blocked_sent)

    return conjoin(all_percept_exprs + combo_var_def_exprs + percept_to_blocked_sent)


def allLegalSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = pacmanSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)


def SLAMSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = SLAMSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)

#______________________________________________________________________________
# Various useful functions, are not needed for completing the project but may be useful for debugging


def modelToString(model: Dict[Expr, bool]) -> str:
    """Converts the model to a string for printing purposes. The keys of a model are 
    sorted before converting the model to a string.
    
    model: Either a boolean False or a dictionary of Expr symbols (keys) 
    and a corresponding assignment of True or False (values). This model is the output of 
    a call to pycoSAT.
    """
    if model == False:
        return "False" 
    else:
        # Dictionary
        modelList = sorted(model.items(), key=lambda item: str(item[0]))
        return str(modelList)


def extractActionSequence(model: Dict[Expr, bool], actions: List) -> List:
    """
    Convert a model in to an ordered list of actions.
    model: Propositional logic model stored as a dictionary with keys being
    the symbol strings and values being Boolean: True or False
    Example:
    >>> model = {"North[2]":True, "P[3,4,0]":True, "P[3,3,0]":False, "West[0]":True, "GhostScary":True, "West[2]":False, "South[1]":True, "East[0]":False}
    >>> actions = ['North', 'South', 'East', 'West']
    >>> plan = extractActionSequence(model, actions)
    >>> print(plan)
    ['West', 'South', 'North']
    """
    plan = [None for _ in range(len(model))]
    for sym, val in model.items():
        parsed = parseExpr(sym)
        if type(parsed) == tuple and parsed[0] in actions and val:
            action, _, time = parsed
            plan[time] = action
    #return list(filter(lambda x: x is not None, plan))
    return [x for x in plan if x is not None]


# Helpful Debug Method
def visualizeCoords(coords_list, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    for (x, y) in itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)):
        if (x, y) in coords_list:
            wallGrid.data[x][y] = True
    print(wallGrid)


# Helpful Debug Method
def visualizeBoolArray(bool_arr, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    wallGrid.data = copy.deepcopy(bool_arr)
    print(wallGrid)

class PlanningProblem:
    """
    This class outlines the structure of a planning problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the planning problem.
        """
        util.raiseNotDefined()

    def getGhostStartStates(self):
        """
        Returns a list containing the start state for each ghost.
        Only used in problems that use ghosts (FoodGhostPlanningProblem)
        """
        util.raiseNotDefined()
        
    def getGoalState(self):
        """
        Returns goal state for problem. Note only defined for problems that have
        a unique goal state such as PositionPlanningProblem
        """
        util.raiseNotDefined()
