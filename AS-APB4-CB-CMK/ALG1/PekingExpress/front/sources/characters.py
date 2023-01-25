from enum import IntEnum


class CharacterType(IntEnum):
    PLAYER = 2
    AI = 3


class Characters:
    def __init__(self, startPosition: int, opBudget: int):
        self.tookPath = []
        self.budget = opBudget
        self.position = startPosition

    def setPosition(self, positionId: int):
        self.position = positionId

    def removeBudget(self, offset: int):
        self.budget -= offset


class AI(Characters):
    pass


class Player(Characters):
    pass
