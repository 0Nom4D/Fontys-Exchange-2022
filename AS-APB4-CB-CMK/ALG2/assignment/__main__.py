#!/usr/bin/env python3
from sys import argv, exit
from os.path import exists
from enum import IntEnum
from os import remove
import numpy as np
import time

from assignment.Graph import Vertex, Graph

from imgui.integrations.pyglet import create_renderer
from pyglet import gl
import pyglet
import imgui

from random import randint, seed

options = {
    'Show Adjacency Matrix': False
}


def impl_pyglet_init(width: int = 1280, height: int = 720):
    window = pyglet.window.Window(width, height, "Algorithm 2 - Programming Assignment", resizable=True)

    gl.glClearColor(.1, .1, .1, .1)

    imgui.create_context()
    impl = create_renderer(window)
    return window, impl


class VertexCoverStatus(IntEnum):
    UNDEFINED = -1,
    FAILED = 0,
    VALID = 1


class App:
    top_pendant_color = (255, 165, 0)
    isolated_color = (255, 0, 255)
    base_color = (255, 255, 255)
    pendant_color = (0, 0, 255)
    top_color = (255, 255, 0)
    vc_color = (0, 255, 0)

    def __init__(self):
        self._required_degree_tops = 1
        self._is_matrix_shown = False
        self._edge_probability = 0.3
        self._vertex_cover_size = 1
        self._vertex_nb = 10

        self._use_greedy = False

        self._show_vertex_cover = False
        self._show_isolated_vertex = False
        self._show_tops_and_pendants = False
        self._vertex_cover_status = VertexCoverStatus.UNDEFINED

        self._graph = Graph(self._vertex_nb)

        self._import_status = -1
        self._import_filename = 'graph.dot'

        self._window = None
        seed(time.time())

    # Export to GraphViz

    def export_to_graphviz(self):
        if exists(self._import_filename):
            remove(self._import_filename)
        with open(self._import_filename, 'x') as fd:
            exported_graph = self._graph.export()
            fd.write(exported_graph)

    # Connect Function

    def connect_graph(self):
        groups = self._graph.get_subgraphs()
        groups_ids = np.unique(np.array(groups))

        i = 2
        while i <= len(groups_ids):
            f_grp = []
            s_grp = []

            for v_id, g_id in enumerate(groups):
                if g_id == (i - 1):
                    f_grp.append(v_id)
                elif g_id == i:
                    s_grp.append(v_id)

            f_vertex = randint(0, len(f_grp) - 1)
            s_vertex = randint(0, len(s_grp) - 1)

            self._graph.matrix.add_edge(f_grp[f_vertex], s_grp[s_vertex])
            i += 1
        self._graph.edges = self._graph.matrix.get_edges()

    # Generate Vertices and Edges

    def generate_graph(self):
        self._graph.reset_vertices()

        window_x, window_y = self._window.get_size()
        for _ in range(self._vertex_nb):
            rand_x, rand_y = randint(100, window_x - 100), randint(100, window_y - 100)
            self._graph.add_vertex(Vertex(rand_x, rand_y))
        self._graph.edges = self._graph.matrix.get_edges()

    # Draw Functions

    def draw_graph(self):
        for v in self._graph.vertices:
            color = self.base_color
            if self._show_tops_and_pendants:
                if v.pendant:
                    color = self.pendant_color
                if v.top:
                    color = self.top_color
            if self._show_vertex_cover and v.covered:
                color = self.vc_color
            if self._show_isolated_vertex and v.isolated:
                color = self.isolated_color
            circle = pyglet.shapes.Circle(v.x, v.y, 4, color=color)
            circle.draw()

        for e in self._graph.edges:
            v1, v2 = self._graph.vertices[e[0]], self._graph.vertices[e[1]]
            color = self.base_color
            if v1.pendant or v2.pendant:
                color = self.pendant_color
            if v1.top or v2.top:
                if v1.pendant or v2.pendant:
                    color = self.top_pendant_color
                else:
                    color = self.top_color
            if self._show_vertex_cover and (v1.covered or v2.covered):
                color = self.vc_color
            line = pyglet.shapes.Line(v1.x, v1.y, v2.x, v2.y, color=color)
            line.draw()

    def draw_color_editor_for_tops_pendants(self):
        is_top_changed, new_top_color = imgui.color_edit3(
            "Top Vertex Color",
            self.top_color[0] / 255,
            self.top_color[1] / 255,
            self.top_color[2] / 255
        )
        if is_top_changed:
            self.top_color = tuple(map(lambda x: int(x * 255), tuple(value for value in new_top_color)))

        is_pendant_changed, new_pendant_color = imgui.color_edit3(
            "Pendant Vertex Color",
            self.pendant_color[0] / 255,
            self.pendant_color[1] / 255,
            self.pendant_color[2] / 255
        )
        if is_pendant_changed:
            self.pendant_color = tuple(map(lambda x: int(x * 255), tuple(value for value in new_pendant_color)))

        is_top_pendant_changed, new_top_pendant_color = imgui.color_edit3(
            "Incident Edges to Top and Pendant Vertex Color",
            self.top_pendant_color[0] / 255,
            self.top_pendant_color[1] / 255,
            self.top_pendant_color[2] / 255
        )
        if is_top_pendant_changed:
            self.top_pendant_color = tuple(map(lambda x: int(x * 255), tuple(value for value in new_pendant_color)))

    def draw_graph_generation_parameters(self) -> None:
        # Slides for Edge Probability and Vertex Number in graph
        _, new_edge_probability = imgui.slider_float(
            "Probability of an edge between 2 vertices", self._edge_probability, 0.001, 1
        )
        _, new_vertex_nb = imgui.slider_int("Number of vertices in the graph", self._vertex_nb, 1, 40)

        if new_edge_probability != self._edge_probability:
            self._edge_probability = new_edge_probability
        if new_vertex_nb != self._vertex_nb:
            self._vertex_nb = new_vertex_nb

        # Button to generate the graph
        # Resets the adjacency matrix, generate the graph and vertices
        if imgui.button('Generate Graph'):
            self._graph.matrix.reset_matrix(self._vertex_nb)
            self._graph.matrix.generate_matrix(self._edge_probability)
            self.generate_graph()

    def draw_connected_graph_section(self) -> None:
        imgui.same_line()
        # Button that connects subgraphs and isolated vertices
        if imgui.button('Connect Graph'):
            self.connect_graph()
        _, self._show_isolated_vertex = imgui.checkbox('Show Isolated Vertices', self._show_isolated_vertex)
        if self._show_isolated_vertex:
            is_isolated_color_changed, isolated_color = imgui.color_edit3(
                'Isolated Vertices Color',
                self.isolated_color[0] / 255,
                self.isolated_color[1] / 255,
                self.isolated_color[2] / 255,
            )
            if isolated_color:
                self.isolated_color = tuple(map(lambda x: int(x * 255), tuple(value for value in isolated_color)))
            isolated_vertices = self._graph.matrix.get_isolated_vertices()
            for v_idx, _ in enumerate(isolated_vertices):
                self._graph.vertices[v_idx].isolated = True
        else:
            imgui.same_line()

    def draw_graph_manip_section(self) -> None:
        # Slider to set up the vertex cover
        imgui.separator()
        imgui.text('Graph Manipulations')
        imgui.bullet_text('Vertex Cover')
        is_color_changed, new_vc_color = imgui.color_edit3(
            "Vertex Cover Color",
            self.vc_color[0] / 255,
            self.vc_color[1] / 255,
            self.vc_color[2] / 255
        )
        if is_color_changed:
            self.vc_color = tuple(map(lambda x: int(x * 255), tuple(value for value in new_vc_color)))

        _, new_vertex_cover_size = imgui.slider_int(
            "Size of vertex cover", self._vertex_cover_size, 1, self._vertex_nb
        )
        if new_vertex_cover_size != self._vertex_cover_size:
            self._vertex_cover_size = new_vertex_cover_size

        # Button to get the vertex cover of size X
        # If no vertex cover can be found with the requested size, it displays a red text telling that
        # the vertex cover of size X can't be found.
        _, self._use_greedy = imgui.checkbox(f'Use Greedy Algorithm for Vertex Cover', self._use_greedy)
        _, self._show_vertex_cover = imgui.checkbox(
            f'Show Vertex Cover of size {self._vertex_cover_size}',
            self._show_vertex_cover
        )
        if self._show_vertex_cover:
            self._show_tops_and_pendants = False
            vc_result = False
            if not self._use_greedy:
                vc_result = self._graph.get_vertex_cover(self._vertex_cover_size, 0)
            else:
                vc_result = self._graph.get_greedy_vertex_cover(self._vertex_cover_size)
            if not vc_result:
                self._vertex_cover_status = VertexCoverStatus.FAILED
            else:
                self._vertex_cover_status = VertexCoverStatus.VALID
        if self._vertex_cover_status == VertexCoverStatus.FAILED:
            imgui.text_colored(f"Vertex cover with size {self._vertex_cover_size} can't be found.", 255, 0, 0)

        imgui.bullet_text('Tops and Pendants')
        self.draw_color_editor_for_tops_pendants()
        _, new_top_required_degree = imgui.slider_int(
            "Required degree for tops", self._required_degree_tops, 1, self._vertex_nb - 1
        )
        if new_top_required_degree != self._required_degree_tops:
            self._required_degree_tops = new_top_required_degree
        _, self._show_tops_and_pendants = imgui.checkbox('Show tops and pendants', self._show_tops_and_pendants)
        if self._vertex_cover_status == VertexCoverStatus.VALID:
            imgui.text_colored('Info: If activated, hides vertex cover.', 255, 0, 0)
        if self._show_tops_and_pendants:
            self._show_vertex_cover = False
            self._graph.get_tops(self._required_degree_tops)
            self._graph.get_pendants()
            self._vertex_cover_status = VertexCoverStatus.UNDEFINED

            if len(self._graph.tops) != self._vertex_nb:
                if imgui.button('Adding Top Vertex', 170):
                    self._graph.add_tops(self._graph.matrix, self._required_degree_tops)
                if len(self._graph.tops) != 0:
                    imgui.same_line(spacing=75)
            if len(self._graph.tops) != 0:
                if imgui.button('Removing random Top Vertex', 225):
                    self._graph.delete_tops(self._graph.matrix, self._required_degree_tops)
            if len(self._graph.pendants) <= self._vertex_nb - 1:
                if imgui.button('Adding Pendant Vertex', 170):
                    self._graph.add_pendant(self._graph.matrix)
                if len(self._graph.pendants) != 0:
                    imgui.same_line(spacing=75)
            if len(self._graph.pendants) != 0:
                if imgui.button('Removing random Pendant Vertex', 225):
                    self._graph.delete_pendant(self._graph.matrix)

    def draw_graph_utils(self):
        # Button to export graph for GraphViz
        imgui.separator()
        imgui.text('Graphviz Utils')
        if self._graph.matrix.generated:
            if imgui.button('Export Graph for GraphViz'):
                self.export_to_graphviz()
        is_file_changed, self._import_filename = imgui.input_text('Imported File', self._import_filename, 256)
        if is_file_changed:
            self._import_status = -1
        if imgui.button('Import Graph from GraphViz'):
            w_x, w_y = self._window.get_size()
            if not self._graph.import_me(self._import_filename, (w_x, w_y)):
                self._import_status = False
        if not self._import_status:
            imgui.text_colored(
                f'An error occurred when importing {self._import_filename}.',
                255, 0, 0
            )

    def draw_window(self):
        imgui.begin("Parameters", False, imgui.WINDOW_ALWAYS_AUTO_RESIZE)
        self.draw_graph_generation_parameters()

        # Checks if matrix is generated
        # If matrix is generated, display buttons and matrix related widgets
        if self._graph.matrix.generated:
            subgraphs = np.array(self._graph.get_subgraphs())

            self._graph.reset_vertices_degree_based_properties()
            self._graph.reset_isolated_status()
            if len(np.unique(subgraphs)) != 1:
                self.draw_connected_graph_section()

            # Checkbox to display the adjacency matrix
            label = 'Show Adjacency Matrix'
            _, self._is_matrix_shown = imgui.checkbox(label, options[label])
            options[label] = self._is_matrix_shown

            if len(np.unique(subgraphs)) == 1:
                self.draw_graph_manip_section()

        # Button to export graph for GraphViz
        self.draw_graph_utils()
        imgui.end()

        # Open a popup showing the adjacency matrix
        # Displays a table containing the adjacency matrix
        if self._is_matrix_shown:
            self.show_adjacency_matrix()

    def show_adjacency_matrix(self):
        imgui.begin("Adjacency Matrix Visualization", False)
        imgui.columns(self._graph.matrix.size, "AdjacencyMatrixViz", False)

        for y_len in range(self._graph.matrix.size):
            for x_len in range(self._graph.matrix.size):
                imgui.text(str(self._graph.matrix.matrix[y_len][x_len]))
                imgui.next_column()
        imgui.columns(1)
        imgui.end()

    # Window Loop

    def launch_app(self) -> int:
        self._window, impl = impl_pyglet_init()

        def update(dt):
            imgui.new_frame()
            self.draw_window()

        def draw(dt):
            update(dt)
            self._window.clear()
            self.draw_graph()
            imgui.render()
            impl.render(imgui.get_draw_data())

        pyglet.clock.schedule_interval(draw, 1 / 120.)
        pyglet.app.run()
        impl.shutdown()
        return 0


def main() -> int:
    if len(argv) != 1:
        return 1
    newApp = App()
    return newApp.launch_app()


if __name__ == "__main__":
    exit(main())
