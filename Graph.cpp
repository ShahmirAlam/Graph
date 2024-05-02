#include "Graph.h"
#include <unordered_map>
#include <fstream>
#include <algorithm>
#include <sstream>
#include <queue>
#include <unordered_set>
#include <cfloat>
#include <limits>

struct nodePath {
    string node;
    nodePath * parent;
    nodePath(string s, nodePath * link) : node(s), parent(link) {}
};

struct DisjointSetNode {
    string node;
    double TH;
    DisjointSetNode * parent;
    DisjointSetNode(string s, double d, DisjointSetNode * link) : node(s), TH(d), parent(link) {
    }
};


DisjointSetNode* findDisjointSet(DisjointSetNode * z) {
    while (z->parent != nullptr) z = z->parent;
    return z;
}
    
void unionDisjointSet(double newThreshold, DisjointSetNode * x, DisjointSetNode * y) {
    x = findDisjointSet(x);
    y = findDisjointSet(y);
    if (x != y) {
        x->parent = y;
        y->TH = newThreshold;
    }
}

unordered_map<string, unordered_map<string, double>> graph;

Graph::Graph(const char* const & edgelist_csv_fn) {
    // Done
    // Design Notes.
    ifstream file(edgelist_csv_fn);
    string line;
    while(getline(file, line)) {
        istringstream s(line);
        string u, v, w;
        getline(s, u, ',');
        getline(s, v, ',');
        getline(s, w, '\n');
        graph[u][v] = graph[v][u] = stod(w);
    }
    file.close();
}


unsigned int Graph::num_nodes() {
    // Done
    return graph.size();
}

vector<string> Graph::nodes() {
    // Done*
    vector<string> nodes;
     for (auto it = graph.begin(); it != graph.end(); ++it) {
        const string& node = it->first;
        nodes.push_back(node);
    }
    return nodes;
}

unsigned int Graph::num_edges() {
    // Done*
    // https://www.geeksforgeeks.org/count-number-edges-undirected-graph/
    unsigned int N = 0;
    for (auto it = graph.begin(); it != graph.end(); ++it) {
        const auto& edges = it->second;
        N += edges.size();
    }
    return N / 2;
}

unsigned int Graph::num_neighbors(string const & node_label) {
    // Done*
     return graph[node_label].size();
}

double Graph::edge_weight(string const & u_label, string const & v_label) {
    // Done*
    //This might have an issue.
    //Return the weight of the edge between a given pair of nodes, 
    //or -1 if there does not exist an edge between the pair of nodes.
    if (!graph[u_label].count(v_label) || !graph.count(u_label) ) return -1;
    return graph[u_label][v_label];
}

vector<string> Graph::neighbors(string const & node_label) {
    // Done*
    vector<string> neighbors;
    for (auto it = graph[node_label].begin(); it != graph[node_label].end(); ++it) {
        const auto& neighbor = it->first;
        neighbors.push_back(neighbor);
    }
    return neighbors;
}

vector<string> Graph::shortest_path_unweighted(string const & start_label, string const & end_label) {
    unordered_map<string, nodePath*> nodeMap;
    queue<nodePath*> nodeList;
    vector<string> path;

    if (start_label == end_label) {
        path.push_back(start_label);
        return path;
    }

    nodeList.push(new nodePath(start_label, nullptr));
    nodeMap[start_label] = nodeList.front();

    while (!nodeList.empty()) {
        nodePath* currentNode = nodeList.front();
        nodeList.pop();

        if (currentNode->node == end_label) {
            //build the path
            while (currentNode->parent != nullptr) {
                path.push_back(currentNode->node);
                currentNode = currentNode->parent;
            }
            path.push_back(currentNode->node);
            reverse(path.begin(), path.end());
            break;
        }

        for (string neighbor : neighbors(currentNode->node)) {
            if (nodeMap.count(neighbor) == 0) {
                nodePath* nextNode = new nodePath(neighbor, currentNode);
                nodeList.push(nextNode);
                nodeMap[neighbor] = nextNode;
            }
        }
    }

    //delete the dynamically allocated memory
    while (!nodeList.empty()) {
        nodePath* current = nodeList.front();
        nodeList.pop();
        delete current;
    }
    nodeMap.clear();
    return path;
}
vector<tuple<string,string,double>> Graph::shortest_path_weighted(string const & start_label, string const & end_label) {
    vector<tuple<string, string, double>> weightedPath;
    unordered_map<string, tuple<double, string, bool>> bestPaths;
    priority_queue<tuple<double, string>, vector<tuple<double, string>>, greater<tuple<double, string>>> nextNodes;

    if (start_label == end_label) {
        weightedPath.push_back(make_tuple(start_label, start_label, -1));
        return weightedPath;
    }

    vector<string> nodeList = nodes();
    for (unsigned int i = 0; i < nodeList.size(); i++) {
        bestPaths[nodeList[i]] = make_tuple(numeric_limits<double>::infinity(), "", false);
    }

    nextNodes.push(make_tuple(0, start_label));
    bestPaths[start_label] = make_tuple(0, "", true);

    while (!nextNodes.empty()) {
        double currLength = get<0>(nextNodes.top());
        string currNode = get<1>(nextNodes.top());
        nextNodes.pop();

        if (currNode == end_label) {
            break;
        }

        vector<string> neighborList = neighbors(currNode);

        for (unsigned int i = 0; i < neighborList.size(); i++) {
            string neighbor = neighborList[i];
            double neighborLength = get<0>(bestPaths[neighbor]);
            bool neighborStatus = get<2>(bestPaths[neighbor]);
            double edgeWeight = edge_weight(currNode, neighbor);
            double newLength = currLength + edgeWeight;

            if (!neighborStatus || newLength < neighborLength) {
                bestPaths[neighbor] = make_tuple(newLength, currNode, true);
                nextNodes.push(make_tuple(newLength, neighbor));
            }
        }
    }

    if (get<2>(bestPaths[end_label]) == false) {
        return weightedPath;
    }

    string currNode = end_label;
    while (currNode != start_label) {
        string prevNode = get<1>(bestPaths[currNode]);
        double edgeWeight = edge_weight(currNode, prevNode);
        weightedPath.push_back(make_tuple(prevNode, currNode, edgeWeight));
        currNode = prevNode;
    }
    reverse(weightedPath.begin(), weightedPath.end());

    return weightedPath;
}

vector<vector<string>> Graph::connected_components(double const& threshold) {
    vector<vector<string>> connectedComponents;
    unordered_map<string, bool> Visted;
    vector<string> nodeList = nodes();

    for (string node : nodeList) Visted[node] = false;

    for (string startNode : nodeList) {
        if (Visted[startNode]) continue;
        queue<string> connectedNodes({startNode});
        vector<string> connectedComponent;

        while (!connectedNodes.empty()) {
            string currNode = connectedNodes.front();
            connectedNodes.pop();
            if (Visted[currNode]) continue;
            Visted[currNode] = true;
            connectedComponent.push_back(currNode);

            for (string neighbor : neighbors(currNode)) {
                if (!Visted[neighbor] && edge_weight(currNode, neighbor) <= threshold) {
                    connectedNodes.push(neighbor);
                }
            }
        }
        connectedComponents.push_back(connectedComponent);
    }
    


    return connectedComponents;
}


double Graph::smallest_connecting_threshold(string const & start_label, string const & end_label) {
    // Done*
    vector<string> nodeList = nodes();
    priority_queue<tuple<double, string, string>, vector<tuple<double, string, string>>, greater<tuple<double, string, string>>> edges;
    if (start_label == end_label) return 0;
    for (const auto& node : nodeList) {
    for (const auto& neighbor : neighbors(node)) edges.push(make_tuple(edge_weight(node, neighbor), node, neighbor));
}
    unordered_map<string, DisjointSetNode *> disjointSetNodes;
    for (const string& node : nodeList) disjointSetNodes.emplace(node, new DisjointSetNode(node, 0, nullptr));
    bool connected = false;
    double threshold = -1;
    while (!connected && !edges.empty()) {
       auto topTuple = edges.top();
       double inputThreshold = std::get<0>(topTuple);
       string x = std::get<1>(topTuple);
       string y = std::get<2>(topTuple);
       edges.pop();

        unionDisjointSet(inputThreshold, findDisjointSet(disjointSetNodes[x]), findDisjointSet(disjointSetNodes[y]));

    if (findDisjointSet(disjointSetNodes[start_label]) == findDisjointSet(disjointSetNodes[end_label])) {
        threshold = findDisjointSet(disjointSetNodes[start_label])->TH;
        connected = true;
    }
}
    for (const string& node : nodeList) {
        delete disjointSetNodes[node];
    }
    return threshold;
}


