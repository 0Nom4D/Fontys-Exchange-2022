from os import close

from sources.characters import Player, AI, CharacterType, Characters
from subprocess import check_output
from enum import IntEnum

from json import dump

import matplotlib.pyplot as plt
import networkx as nx


class Vertex:
    def __init__(self, index, critical=False):
        self.index = index
        self.critical = critical
        self.neighbours = {}

    def add_neighbour(self, vertex, weight=0):
        self.neighbours[vertex] = weight

    def remove_neighbour(self, vertex):
        del self.neighbours[vertex]

    def get_neighbours(self):
        return list(self.neighbours.keys())

    def weight(self, vertex):
        return self.neighbours[vertex]

    def set_critical(self, critical):
        self.critical = critical


class PEGraph:
    def __init__(self):
        self.vertices = {}
        self.num_vertices = 0

    def add_edge(self, u: int, v: int, weight: int):
        added_vertices = 0
        if u not in self.vertices:
            self.vertices[u] = Vertex(u)
            added_vertices += 1
        if v not in self.vertices:
            self.vertices[v] = Vertex(v)
            added_vertices += 1
        self.vertices[u].add_neighbour(v, weight)
        self.vertices[v].add_neighbour(u, weight)
        self.num_vertices += added_vertices

    def get_vertices(self):
        return self.vertices

    def get_vertex(self, u: int):
        return self.vertices[u] if u in self.vertices else None

    def update_critical(self, u: int, critical=True):
        vertex = self.get_vertex(u)
        vertex.set_critical(critical)


class GameState(IntEnum):
    VICTORY = 1
    DRAW = 0
    DEFEAT = -1


def createGraph(options):
    g = PEGraph()

    for i in range(len(options['Roads']['a'])):
        g.add_edge(options['Roads']['a'][i], options['Roads']['b'][i], options['Roads']['price'][i])
    for i in range(len(options['Locations']['critical'])):
        g.update_critical(options['Locations']['critical'][i], True)
    return g


class GraphDrawer:
    def __init__(self, options):
        self.graph = createGraph(options)

        self.drawing_options = options
        self.ai = AI(options['StartLocation'], options['Budget'])
        self.player = Player(options['StartLocation'], 1)
        self.vertices = self.getUniqueVertices()

    def getUniqueVertices(self):
        vertices = []
        sample = self.drawing_options['Roads']['a'] + self.drawing_options['Roads']['b']

        for v in sample:
            if v not in vertices:
                vertices.append(v)
        return vertices

    def drawGraph(self):
        G = nx.Graph()

        color_map = [None for i in range(len(self.vertices))]
        for index, vertex in enumerate(self.vertices):
            if vertex == self.player.position and vertex == self.ai.position:
                color_map[index] = 'black'
            elif vertex == self.player.position:
                color_map[index] = 'green'
            elif vertex == self.ai.position:
                color_map[index] = 'red'
            else:
                color_map[index] = 'blue'
        for i in range(len(self.drawing_options['Roads']['a'])):
            G.add_edge(
                self.drawing_options['Roads']['a'][i],
                self.drawing_options['Roads']['b'][i],
                weight=self.drawing_options['Roads']['price'][i]
            )
        pos = nx.spring_layout(G)
        nx.draw_networkx(G, pos, font_color="whitesmoke")
        labels = nx.get_edge_attributes(G, 'weight')
        nx.draw_networkx_nodes(G, pos, nodelist=self.vertices, node_color=color_map)
        nx.draw_networkx_edge_labels(G, pos, edge_labels=labels)

    def getGameResult(self) -> int:
        if self.player.position != 88 and self.ai.position == 88:
            print('AI won!')
            return GameState.DEFEAT
        elif self.player.position == 88 and self.ai.position != 88:
            print('Player won!')
            return GameState.VICTORY
        print('Player and AI draw!')
        return GameState.DRAW

    def updateCharacterPosition(self, c: Characters, destination: int):
        fromPosition = self.graph.get_vertex(c.position)
        weightFromPosition = fromPosition.weight(destination)
        c.removeBudget(weightFromPosition)
        c.setPosition(destination)

    def playAITurn(self):
        ai_data = self.drawing_options
        ai_data['StartLocation'] = self.ai.position
        ai_data['Budget'] = self.ai.budget

        with open("ai_data.json", 'w') as write:
            dump(ai_data, write)
        stdout = check_output(['../ai/.stack-work/dist/x86_64-osx/Cabal-3.4.1.0/build/ai-exe/ai-exe', '-f', 'ai_data.json', '-p', f'{self.player.position}'])
        dest = int(stdout)
        if dest != self.ai.position:
            self.updateCharacterPosition(self.ai, dest)
        self.drawGraph()
        plt.show()

    def playPlayersTurn(self):
        dest = None
        while dest is None:
            input_value = int(input('Where do you want to go? '))
            if input_value not in self.vertices:
                print("Destination doesn't exists.")
                continue
            dest = int(input_value)
            if self.graph.get_vertex(self.player.position).weight(dest) > self.player.budget:
                print(f'Not enough budget to go to node {dest}.')
                dest = None
                continue
            elif self.graph.get_vertex(dest).critical and self.ai.position == dest or dest not in self.graph.get_vertex(self.player.position).get_neighbours():
                print('Invalid move.')
                dest = None
                continue
        if dest != self.player.position:
            self.updateCharacterPosition(self.player, dest)
        self.drawGraph()
        plt.show()

    def launchGame(self, userFirst: bool) -> int:
        while (self.player.position != 88 and self.ai.position != 88) or (self.player.budget == 0 or self.player.budget == 0):
            aiPlayed = playerPlayed = False
            if userFirst:
                self.playPlayersTurn()
                playerPlayed = True
            else:
                self.playAITurn()
                aiPlayed = True
            if playerPlayed:
                self.playAITurn()
            elif aiPlayed:
                self.playPlayersTurn()
        return self.getGameResult()
