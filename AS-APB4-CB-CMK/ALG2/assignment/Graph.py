from typing import Tuple, Set, List
from random import randint
from os.path import exists
from os import stat

from assignment.Matrix import AdjacencyMatrix, Edge


class Vertex:
    def __init__(self, x, y, isolated=False):
        self._x = x
        self._y = y
        self._top = False
        self._covered = False
        self._pendant = False
        self._isolated = isolated

    def reset_degree_based_property(self):
        self._pendant = False
        self._top = False

    def reset_covered(self):
        self._covered = False

    def reset_isolated(self):
        self._isolated = False

    @property
    def isolated(self) -> bool:
        return self._isolated

    @isolated.setter
    def isolated(self, new_value: bool):
        self._isolated = new_value

    @property
    def covered(self) -> bool:
        return self._covered

    @covered.setter
    def covered(self, new_value: Tuple[int, int, int]):
        self._covered = new_value

    @property
    def top(self) -> bool:
        return self._top

    @top.setter
    def top(self, new_value: bool):
        self._top = new_value

    @property
    def pendant(self) -> bool:
        return self._pendant

    @pendant.setter
    def pendant(self, new_value: bool):
        self._pendant = new_value

    @property
    def x(self) -> int:
        return self._x

    @property
    def y(self) -> int:
        return self._y


class Graph:
    def __init__(self, vertex_nb: int):
        self._vertices: List[Vertex] = []
        self._edges: Set[Tuple[int, int]] = set()

        self._pendants: List[int] = []
        self._tops: List[int] = []

        self._vertex_nb = vertex_nb

        self._matrix = AdjacencyMatrix(self._vertex_nb)

    # Graph Connection Utils

    def get_vertices_connections(self) -> List[Set[int]]:
        connections = []

        for i in range(self._vertex_nb):
            related_edges = [item for item in self._edges if item[0] == i or item[1] == i]

            group_vertex: Set[int] = set()
            for edge in related_edges:
                if edge[0] == i and edge[1] != i:
                    group_vertex.add(edge[1])
                elif edge[0] != i and edge[1] == i:
                    group_vertex.add(edge[0])
            connections.append(group_vertex)
        return connections

    def get_subgraphs(self) -> List[int]:
        def are_all_vertices_in_group(lst: List[int]):
            for g_idx in lst:
                if g_idx == 0:
                    return False
            return True

        def get_next_ungrouped_vertex(lst: List[int]) -> int:
            for v_idx, g_id in enumerate(lst):
                if g_id == 0:
                    return v_idx
            return -1

        connections = self.get_vertices_connections()
        groups = [0 for _ in range(self._vertex_nb)]
        current_vertex = 0
        group_id = 1

        while not are_all_vertices_in_group(groups):
            process_list = [current_vertex]
            for idx in process_list:
                if groups[idx] == 0:
                    groups[idx] = group_id
                    process_list += connections[idx]
            current_vertex = get_next_ungrouped_vertex(groups)
            group_id += 1
        return groups

    def reset_vertex_cover(self):
        for vertex in self._vertices:
            vertex.reset_covered()

    def reset_vertices_degree_based_properties(self):
        for vertex in self._vertices:
            vertex.reset_degree_based_property()

    def reset_isolated_status(self):
        for vertex in self._vertices:
            vertex.reset_isolated()

    def get_tops(self, required_size: int):
        self._tops = []
        connections = self.get_vertices_connections()

        for v_idx, connected in enumerate(connections):
            if len(connected) > required_size:
                self._vertices[v_idx].top = True
                self._tops.append(v_idx)

    def get_pendants(self):
        self._pendants = []
        connections = self.get_vertices_connections()

        for v_idx, connected in enumerate(connections):
            if len(connected) == 1:
                self._vertices[v_idx].pendant = True
                self._pendants.append(v_idx)

    def add_pendant(self, matrix: AdjacencyMatrix):
        non_pendant_vertices = [v_idx for v_idx in range(self._vertex_nb)
                                if v_idx not in self.pendants]
        v_idx = non_pendant_vertices[randint(0, len(non_pendant_vertices) - 1)]
        connections = self.get_vertices_connections()
        connected_vertices = list(connections[v_idx])
        unconnected_vertices = [idx for idx in [_ for _ in range(self._vertex_nb)]
                                if idx not in connected_vertices and idx != v_idx]

        while len(connected_vertices) > 1:
            to_remove = connected_vertices[randint(0, len(connected_vertices) - 1)]
            while len(connections[to_remove]) <= 1:
                to_remove = connected_vertices[randint(0, len(connected_vertices) - 1)]
            matrix.remove_edge(v_idx, to_remove)
            unconnected_vertices.append(to_remove)
            connected_vertices.remove(to_remove)
        self._pendants.append(v_idx)
        self._edges = matrix.get_edges()

    def delete_pendant(self, matrix: AdjacencyMatrix):
        v_idx = self._pendants[randint(0, len(self._pendants) - 1)]
        connected_vertices = list(self.get_vertices_connections()[v_idx])
        unconnected_vertices = [idx for idx in [_ for _ in range(self._vertex_nb)]
                                if idx not in connected_vertices and v_idx != idx]
        to_connect = 0
        while len(connected_vertices) <= 1:
            to_connect = unconnected_vertices[randint(0, len(unconnected_vertices) - 1)]
            while matrix.matrix[v_idx][to_connect] == 1:
                to_connect = unconnected_vertices[randint(0, len(unconnected_vertices) - 1)]
            matrix.add_edge(v_idx, to_connect)
            connected_vertices.append(to_connect)
        self._pendants.remove(v_idx)
        if to_connect in self._pendants:
            self._pendants.remove(to_connect)
        self._edges = matrix.get_edges()

    def add_tops(self, matrix: AdjacencyMatrix, size: int):
        connected_vertices = self.get_vertices_connections()
        possible_vertices = [v_idx for v_idx in range(self._vertex_nb) if len(connected_vertices[v_idx]) < size]
        tops_v_id = possible_vertices[randint(0, len(possible_vertices) - 1)]
        connected_vertices = list(connected_vertices[tops_v_id])
        unconnected_vertices = [v_idx for v_idx in [_ for _ in range(self._vertex_nb)]
                                if v_idx not in connected_vertices and v_idx != tops_v_id]

        while len(connected_vertices) <= size:
            to_connect = unconnected_vertices[randint(0, len(unconnected_vertices) - 1)]
            if len(unconnected_vertices) == 0:
                break
            if to_connect == tops_v_id:
                continue
            matrix.add_edge(tops_v_id, to_connect)
            connected_vertices.append(to_connect)
        self._tops.append(tops_v_id)
        self._edges = matrix.get_edges()

    def delete_tops(self, matrix: AdjacencyMatrix, size: int):
        connected_vertices = self.get_vertices_connections()
        possible_vertices = [v_idx for v_idx in range(self._vertex_nb) if len(connected_vertices[v_idx]) >= size]
        tops_v_id = possible_vertices[randint(0, len(possible_vertices) - 1)]
        connected_vertices = list(connected_vertices[tops_v_id])
        unconnected_vertices = [v_idx for v_idx in [_ for _ in range(self._vertex_nb)]
                                if v_idx not in connected_vertices and v_idx != tops_v_id]

        while len(connected_vertices) > size:
            to_connect = connected_vertices[randint(0, len(connected_vertices) - 1)]
            if to_connect == tops_v_id:
                continue
            matrix.remove_edge(tops_v_id, to_connect)
            unconnected_vertices.append(to_connect)
            connected_vertices.remove(to_connect)
        self._tops.remove(tops_v_id)
        self._edges = matrix.get_edges()

    # Vertex Cover

    def get_vertex_cover(self, need_size: int, current_size: int) -> bool:
        if current_size == 0:
            for vertex in self._vertices:
                vertex.covered = False
        elif current_size == need_size:
            for edge in self._edges:
                if not self._vertices[edge[0]].covered and not self._vertices[edge[1]].covered:
                    return False
            return True
        for v_idx in range(self._vertex_nb):
            if self._vertices[v_idx].covered:
                continue
            self._vertices[v_idx].covered = True
            if self.get_vertex_cover(need_size, current_size + 1):
                return True
            self._vertices[v_idx].covered = False
        return False

    def get_greedy_vertex_cover(self, required_size: int) -> bool:
        vertex_cover: Set[int] = set()

        self.reset_vertex_cover()
        def check_vertex_cover() -> Tuple[bool, List[int]]:
            edges: List[int] = [0] * self._vertex_nb
            is_valid = True

            for y_len in range(self._vertex_nb):
                for x_len in range(self._vertex_nb):
                    if self._matrix.matrix[y_len][x_len] == int(Edge.LINK):
                        if y_len not in vertex_cover and x_len not in vertex_cover:
                            is_valid = False
                            edges[y_len] += 1
                            edges[x_len] += 1
            return is_valid, edges

        is_vc_valid, nb_edges = check_vertex_cover()
        while not is_vc_valid:
            if len(vertex_cover) >= required_size:
                break
            maximum_degree_vertex_id = [v_idx for v_idx in range(self._vertex_nb)
                                        if nb_edges[v_idx] == max(nb_edges) and v_idx not in vertex_cover][0]
            vertex_cover.add(maximum_degree_vertex_id)
            self._vertices[maximum_degree_vertex_id].covered = True
            is_vc_valid, nb_edges = check_vertex_cover()
        if not is_vc_valid:
            self.reset_vertex_cover()
            return False

        connections_lengths = [-1] * self._vertex_nb
        for v_idx in range(self._vertex_nb):
            if v_idx in vertex_cover:
                continue
            connections_lengths[v_idx] = self._matrix.matrix[v_idx].count(1)
        while len(vertex_cover) != required_size:
            maximum_degree_vertex_id = [v_idx for v_idx in range(self._vertex_nb)
                                        if connections_lengths[v_idx] == max(connections_lengths)][0]
            vertex_cover.add(maximum_degree_vertex_id)
            self._vertices[maximum_degree_vertex_id].covered = True
            connections_lengths[maximum_degree_vertex_id] = -1
        return True

    # Vertices

    def reset_vertices(self):
        self._vertices = []
        self.vertex_nb = 0

    def add_vertex(self, new_vertex: Vertex):
        self._vertices.append(new_vertex)
        self.vertex_nb = len(self._vertices)

    # Graph Export / Import

    def export(self) -> str:
        export = ""
        export += "graph my_graph {" \
                  "\n\tnode [ fontname = Arial, size=\"500,500!\",style=\"filled,setlinewidth(4)\", shape=circle ]"
        for v_idx in range(self._vertex_nb):
            color = "#4040F040"
            if self._vertices[v_idx].covered:
                color = "#F0404040"
            export += f"\n\tnode{v_idx} [ label = \"{v_idx}\" color=\"{color}\" ]"
        for y_len in range(self._vertex_nb):
            for x_len in range(y_len + 1, self._vertex_nb):
                if self._matrix.matrix[y_len][x_len] == 1:
                    if self._vertices[x_len].covered or self._vertices[y_len].covered:
                        export += f"\n\tnode{x_len} -- node{y_len} [ color=blue ]"
                    else:
                        export += f"\n\tnode{x_len} -- node{y_len} [ color=black ]"
        export += "\n}"
        return export

    def import_me(self, import_file_name: str, window_size: Tuple[int, int]) -> bool:
        line_idx = 0
        created_vertices: List[str] = []
        if not exists(import_file_name) or stat(import_file_name) == 0:
            return False

        self._matrix.reset_matrix(self._matrix.size)
        self.reset_vertices()
        window_x, window_y = window_size
        with open(import_file_name) as fd:
            for line in fd:
                if line_idx < 2 or '}' in line:
                    line_idx += 1
                    continue

                line = line.lstrip().rstrip().rstrip('\n')
                l_parsed = line.split(' ')
                if "--" in l_parsed:
                    if l_parsed[0] not in created_vertices or l_parsed[2] not in created_vertices:
                        self.reset_vertices()
                        return False
                    self._matrix.add_edge(created_vertices.index(l_parsed[0]), created_vertices.index(l_parsed[2]))
                else:
                    rand_x, rand_y = randint(100, window_x - 100), randint(100, window_y - 100)
                    self.add_vertex(Vertex(rand_x, rand_y))
                    created_vertices.append(l_parsed[0])
        self._edges = self._matrix.get_edges()
        self._matrix.generated = True
        return True

    # Properties

    @property
    def matrix(self) -> AdjacencyMatrix:
        return self._matrix

    @matrix.setter
    def matrix(self, new_matrix: AdjacencyMatrix):
        self._matrix = new_matrix

    @property
    def vertices(self) -> List[Vertex]:
        return self._vertices

    @vertices.setter
    def vertices(self, vertices: List[Vertex]):
        self._vertices = vertices
        self.vertex_nb = len(self._vertices)

    @property
    def pendants(self) -> List[int]:
        return self._pendants

    @property
    def tops(self) -> List[int]:
        return self._tops

    @property
    def vertex_nb(self) -> int:
        return self._vertex_nb

    @vertex_nb.setter
    def vertex_nb(self, new_nb: int):
        self._vertex_nb = new_nb

    @property
    def edges(self) -> Set[Tuple[int, int]]:
        return self._edges

    @edges.setter
    def edges(self, new_edges: Set[Tuple[int, int]]):
        self._edges = new_edges
