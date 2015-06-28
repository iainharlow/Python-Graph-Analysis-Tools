"""
A set of algorithmically efficient tools for graph and network analysis.
These tools can be used to analyse the connectivity of directed and 
undirected graphs, and to measure robustness to network disruption.
To use these, your graph should be represented as a dictionary.
"""

# general imports
import math
import random
from collections import deque

###################################
# Example graph structure

example_directed_graph = {0:[1,2],1:[0,3],2:[1],3:[0,1,2]}
example_undirected_graph = {0:[1,2],1:[0],2:[0,3],3:[2]}



###################################
# Graph Functions

def make_complete_graph(num_nodes):
    """
    Function to create a dictionary representation of
    a complete undirected graph with num_nodes nodes.
    """
    graph_list = []
    for node in range(num_nodes):
        temp_set = set(range(num_nodes))
        temp_set.remove(node)
        graph_list.append(temp_set)
    graph = dict(enumerate(graph_list))
    return graph

def compute_in_degrees(ugraph):
    """
    Takes an undirected graph ugraph (represented as a 
    dictionary) and computes the in-degrees for the 
    nodes in the graph.
    """
    in_degrees = dict((node,len(ugraph[node])) for node in ugraph)
    return in_degrees 

def in_degree_distribution(digraph):
    """
    Takes a directed graph digraph (represented as a
    dictionary) and computes the unnormalized 
    distribution of the in-degrees of the graph.
    """
    degrees = compute_in_degrees(digraph)
    degree_hist = dict((value,0) for value in range(len(digraph)))
    for node in degrees:
        degree_hist[degrees[node]] += 1
    zeros = []
    for degree, number in degree_hist.items():
        if number == 0:
            zeros.append(degree)
    for degree in zeros:
        degree_hist.pop(degree)
    return degree_hist

def number_of_edges(ugraph):
    """
    Takes an undirected graph ugraph (represented as a 
    dictionary) and computes the total number of edges
    in the graph.
    """
    edges = 0
    for node in ugraph:
        edges += len(ugraph[node])
    return edges//2 

def copy_graph(graph):
    """
    Make a copy of a graph
    """
    new_graph = {}
    for node in graph:
        new_graph[node] = set(graph[node])
    return new_graph

def delete_node(ugraph, node):
    """
    Delete a node from an undirected graph
    """
    neighbors = ugraph[node]
    ugraph.pop(node)
    for neighbor in neighbors:
        ugraph[neighbor].remove(node)
    
def targeted_order(ugraph):
    """
    Compute a targeted attack order consisting
    of nodes of maximal degree
    
    Returns:
    A list of nodes
    """
    # copy the graph
    new_graph = copy_graph(ugraph)
    
    order = []    
    while len(new_graph) > 0:
        max_degree = -1
        for node in new_graph:
            if len(new_graph[node]) > max_degree:
                max_degree = len(new_graph[node])
                max_degree_node = node
        
        neighbors = new_graph[max_degree_node]
        new_graph.pop(max_degree_node)
        for neighbor in neighbors:
            new_graph[neighbor].remove(max_degree_node)

        order.append(max_degree_node)
    return order

def fast_targeted_order(ugraph):
    """
    Compute a targeted attack order consisting
    of nodes of maximal degree
    
    Returns:
    A list of nodes
    """
    # copy the graph
    new_graph = copy_graph(ugraph)
    
    degree_sets = [set() for dummy_idx in range(len(new_graph))]

    for node in new_graph:
        degree = len(new_graph[node])
        degree_sets[degree].add(node)
    
    order = []
    
    for degree in range(len(new_graph)-1,-1,-1):
        while degree_sets[degree] != set():
            node_u = degree_sets[degree].pop()
            for neighbour in new_graph[node_u]:
                neighbour_degree = len(new_graph[neighbour])
                degree_sets[neighbour_degree].remove(neighbour)
                degree_sets[neighbour_degree-1].add(neighbour)
            order.append(node_u)
            delete_node(new_graph,node_u)

    return order

def bfs_visited(ugraph, start_node):
    """
    Function to implement the breadth-first search
    algorithm.
    """
    queue = deque()
    visited = set([start_node])
    queue.append(start_node)
    while len(queue)>0:
        node_j = queue.popleft()
        for neighbour in ugraph[node_j]:
            if neighbour not in visited:
                visited.add(neighbour)
                queue.append(neighbour)
    return visited

def cc_visited(ugraph):
    """
    Function to extract all connected components in a
    graph, using breadth-first search.
    """
    remaining_nodes = set(ugraph.keys())
    components = []
    while len(remaining_nodes)>0:
        node_i = remaining_nodes.pop()
        w_nodes = bfs_visited(ugraph,node_i)
        components.append(w_nodes)
        remaining_nodes = remaining_nodes.difference(w_nodes)
    return components

def largest_cc_size(ugraph):
    """
    Function to find the size of the largest connected
    component in a graph.
    """
    components = cc_visited(ugraph)
    cc_sizes = [len(component) for component in components]
    if len(cc_sizes) == 0:
        cc_sizes = [0]
    return max(cc_sizes)

def compute_resilience(ugraph,attack_order):
    """
    Removes the nodes listed in attack_order one-by-one
    and returns a list of the largest remaining connected
    component after each attack (and before any attacks).
    """
    component_list=[largest_cc_size(ugraph)]
    temp_graph = copy_graph(ugraph)
    for attack in attack_order:
        neighbours = temp_graph.pop(attack)
        for node in neighbours:
            temp_graph[node].remove(attack)
        component_list.append(largest_cc_size(temp_graph))
    return component_list

def make_ER_graph(num_nodes,p):
    """
    Function to create a dictionary representation of
    an undirected ER graph with num_nodes nodes and
    edge probability p.
    """
    graph_list = [set([]) for dummy_i in range(num_nodes)]
    for node_a in range(num_nodes):
        for node_b in range(num_nodes):
            if node_a < node_b and random.random() < p:
                graph_list[node_a].add(node_b)
                graph_list[node_b].add(node_a)    
    graph = dict(enumerate(graph_list))
    return graph

def make_UPA_graph(num_nodes,m):
    """
    Function to create a dictionary representation of
    an undirected UPA graph with num_nodes nodes and
    mean number of edges m.
    """
    ugraph = make_complete_graph(m)
    node_chooser = [node for node in range(m) for dummy_idx in range(m)]
    
    for n in range(num_nodes-m):
        neighbours = [random.choice(node_chooser) for dummy_idx in range(m)]
        neighbour_set = set(neighbours)
        ugraph[m+n] = neighbour_set
        node_chooser.extend([m+n]*(len(neighbour_set)+1))
        for neighbour in neighbour_set:
            ugraph[neighbour].add(m+n)
            node_chooser.append(neighbour)
    return ugraph

def random_order(ugraph):
    """
    Takes a graph and returns a list of its nodes in a random order.
    """
    nodes = list(ugraph.keys())
    random.shuffle(nodes)
    return nodes



