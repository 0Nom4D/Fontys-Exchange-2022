# Algorithm 2 - Programming Assignment

## How to launch?

This program can be launch with the assignment.sh script.

```txt
$> ./assignment.sh
```

## Functionalities

### Generation

You can generate a graph with a customized edge probability for each pair of vertex.

Both of these values can be customized with sliders:

- The edge probability between each edge is between 0.001 and 1.
- The number of vertices is between 1 and 40.

Once the graph is generated, we can connect the graph until all vertices form a single subgraph.

### Graph Manipulations

#### Isolated Vertices

If the graph is not connected, you can display isolated vertices and change their color.

#### Vertex Cover

#### Brute-Force Algorithm

When the graph is connected, we can get the vertex cover using a 'bruteforce' algorithm. You can configure the required vertex cover size.

#### Greedy Algorithm

When the graph is connected, we can get the vertex cover using the 'greedy' algorithm. You can configure the size.

Even if a tinier vertex cover exists using a 'casual' greedy algorithm, the minimum vertex cover found will be the tiner that algorithm can find.

In both cases, if the vertex cover of that size can't be found, a red colored message will be displayed telling you the vertex cover can't be found.

#### Tops and Pendants

NOTE: Please note that pendant adding is maybe weird because I didn't know when to stop the pendant adding method.

When the graph is connected, you can configure tops and pendants vertices:

- Their color can be change using color selector.
- The required size to determine a top vertex can be customized using the slider.

To show the vertices, you can click on the checkbox to display with colors the tops and pendants vertices.

Buttons will appear giving you the option of:

- Adding a pendant vertex by removing edges to a random non-pendant vertex by removing edges that edge until there's one left.
- Removing random pendant vertex by adding one edge to a pendant vertex.
- Adding a top vertex by adding edges to a random non-top vertex until this vertex is incident to X vertices, where X is the required size to detect a top
- Removing a top vertex by removing edges to a random top vertex until it is not considered a top vertex anymore.

### Imports / Exports

#### Import

You can also import a '.dot' file from GraphViz.

The GraphViz import don't care about colors or covered vertices.

#### Export

If the graph is generated, you can export your graph using the 'Export Graph' button. It will create a 'graph.dot' file and append your export content in it.

If the file already exists, it will be deleted and re-created.
