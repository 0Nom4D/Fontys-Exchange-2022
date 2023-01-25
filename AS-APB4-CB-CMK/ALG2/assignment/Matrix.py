from random import random, seed
from typing import List, Union, Tuple, Set

from enum import IntEnum


class Edge(IntEnum):
    UNLINK = 0
    LINK = 1


class AdjacencyMatrix:
    def __init__(self, size):
        self._matrix = [[0 for _ in range(size)] for _ in range(size)]
        self._size = size

        self._generated = False

    def generate_matrix(self, edge_probability: float) -> List[List[int]]:
        for i in range(self._size):
            for j in range(self._size):
                if self._matrix[i][j] == Edge.LINK or self._matrix[j][i] == Edge.LINK or i == j:
                    continue
                value = random()
                if value <= edge_probability:
                    self._matrix[i][j] = int(Edge.LINK)
                    self._matrix[j][i] = int(Edge.LINK)
        self._generated = True
        return self._matrix

    def reset_matrix(self, size: Union[int, None]) -> List[List[int]]:
        if size is not None:
            self.size = size

        self._matrix = [[0 for _ in range(self._size)] for _ in range(self._size)]
        return self._matrix

    def get_isolated_vertices(self) -> List[int]:
        isolated_vertices: List[int] = []

        for y_len in range(self._size):
            if 1 not in self._matrix[y_len]:
                isolated_vertices.append(y_len)
        return isolated_vertices

    def add_edge(self, y_len: int, x_len: int):
        self._matrix[y_len][x_len] = int(Edge.LINK)
        self._matrix[x_len][y_len] = int(Edge.LINK)

    def remove_edge(self, y_len: int, x_len: int):
        self._matrix[y_len][x_len] = int(Edge.UNLINK)
        self._matrix[x_len][y_len] = int(Edge.UNLINK)

    def get_edges(self) -> Set[Tuple[int, int]]:
        edges = set()

        for y_len in range(self._size):
            for x_len in range(self._size):
                if self._matrix[y_len][x_len] == Edge.LINK:
                    edges.add((y_len, x_len))
        return edges

    @property
    def size(self) -> int:
        return self._size

    @size.setter
    def size(self, value: int):
        self._size = value

    @property
    def matrix(self) -> List[List[int]]:
        return self._matrix

    @matrix.setter
    def matrix(self, matrix_size: int):
        self._matrix = [[0 for _ in range(matrix_size)] for _ in range(matrix_size)]

    @property
    def generated(self):
        return self._generated

    @generated.setter
    def generated(self, value: bool):
        self._generated = value
