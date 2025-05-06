#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
#include <limits>
#include <unordered_map>
#include <set>
#include <cmath>
#include <ctime>
#include <stack>
#include <iomanip>
#include <fstream>
#include <sstream>

using namespace std;

// ==================== Advanced Data Structures ====================

// Trie for station name autocomplete
class TrieNode {
public:
    unordered_map<char, TrieNode*> children;
    bool isEnd;
    int stationIndex;

    TrieNode() : isEnd(false), stationIndex(-1) {}
};

class StationTrie {
private:
    TrieNode* root;

    void findAllWords(TrieNode* node, string currentPrefix, vector<pair<string, int>>& results) {
        if (node->isEnd) {
            results.emplace_back(currentPrefix, node->stationIndex);
        }

        for (auto& child : node->children) {
            findAllWords(child.second, currentPrefix + child.first, results);
        }
    }

public:
    StationTrie() {
        root = new TrieNode();
    }

    void insert(const string& word, int index) {
        TrieNode* current = root;
        for (char ch : word) {
            char lowerCh = tolower(ch);
            if (current->children.find(lowerCh) == current->children.end()) {
                current->children[lowerCh] = new TrieNode();
            }
            current = current->children[lowerCh];
        }
        current->isEnd = true;
        current->stationIndex = index;
    }

    vector<pair<string, int>> searchPrefix(const string& prefix) {
        vector<pair<string, int>> results;
        TrieNode* current = root;

        for (char ch : prefix) {
            char lowerCh = tolower(ch);
            if (current->children.find(lowerCh) == current->children.end()) {
                return results;
            }
            current = current->children[lowerCh];
        }

        findAllWords(current, prefix, results);
        return results;
    }
};

// Disjoint Set Union (DSU) for connected components
class DSU {
private:
    vector<int> parent;
    vector<int> rank;

public:
    DSU(int n) {
        parent.resize(n);
        rank.resize(n, 0);
        for (int i = 0; i < n; ++i) {
            parent[i] = i;
        }
    }

    int find(int u) {
        if (parent[u] != u) {
            parent[u] = find(parent[u]);
        }
        return parent[u];
    }

    void unionSets(int u, int v) {
        int rootU = find(u);
        int rootV = find(v);

        if (rootU != rootV) {
            if (rank[rootU] > rank[rootV]) {
                parent[rootV] = rootU;
            } else if (rank[rootU] < rank[rootV]) {
                parent[rootU] = rootV;
            } else {
                parent[rootV] = rootU;
                rank[rootU]++;
            }
        }
    }

    bool isConnected(int u, int v) {
        return find(u) == find(v);
    }
};

// ==================== Route Planner Class ====================

class RoutePlanner {
private:
    vector<string> stations;
    vector<vector<int>> costMatrix;
    vector<vector<int>> timeMatrix;
    vector<vector<pair<int, int>>> adjCost; // {cost, time}
    vector<vector<pair<int, int>>> adjTime; // {time, cost}
    DSU dsu;
    StationTrie trie;
    unordered_map<int, vector<pair<int, int>>> trafficUpdates; // station -> {time, delay}
    vector<vector<int>> allPairsCost;
    vector<vector<int>> allPairsTime;
    vector<vector<int>> nextHopCost;
    vector<vector<int>> nextHopTime;
    bool precomputedAllPairs;
    unordered_map<string, vector<pair<vector<int>, int>>> favoriteRoutes; // user -> {path, criteria}

    // Heuristic function for A* (Euclidean distance approximation)
    double heuristic(int a, int b) {
        // In real implementation, use actual coordinates
        return abs(a - b) * 10.0;
    }

    // Get time between stations (with possible traffic)
    int getTimeWithTraffic(int u, int v) {
        int baseTime = timeMatrix[u][v];
        if (baseTime == INT_MAX) return baseTime;

        // Check for traffic updates
        for (auto& [station, delay] : trafficUpdates[u]) {
            if (station == v) {
                return baseTime + delay;
            }
        }

        return baseTime;
    }

public:
    RoutePlanner(const vector<string>& stationNames, const vector<vector<int>>& paths)
        : stations(stationNames), dsu(stationNames.size()), precomputedAllPairs(false) {

        int n = stations.size();
        costMatrix.resize(n, vector<int>(n, INT_MAX));
        timeMatrix.resize(n, vector<int>(n, INT_MAX));
        adjCost.resize(n);
        adjTime.resize(n);

        // Initialize trie for station names
        for (int i = 0; i < stations.size(); ++i) {
            trie.insert(stations[i], i);
        }

        // Build adjacency lists and matrices
        for (const auto& path : paths) {
            int u = path[0];
            int v = path[1];
            int cost = path[2];
            int time = path[3];

            adjCost[u].emplace_back(v, cost);
            adjCost[v].emplace_back(u, cost);
            adjTime[u].emplace_back(v, time);
            adjTime[v].emplace_back(u, time);

            costMatrix[u][v] = costMatrix[v][u] = cost;
            timeMatrix[u][v] = timeMatrix[v][u] = time;

            dsu.unionSets(u, v);
        }

        // Initialize diagonal
        for (int i = 0; i < n; ++i) {
            costMatrix[i][i] = 0;
            timeMatrix[i][i] = 0;
        }
    }

    // ==================== Pathfinding Algorithms ====================

    // Dijkstra's algorithm for minimum cost path
    int dijkstraCost(int src, int des, vector<int>& parent) {
        int n = stations.size();
        vector<int> dist(n, INT_MAX);
        priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> pq;

        dist[src] = 0;
        parent[src] = src;
        pq.emplace(0, src);

        while (!pq.empty()) {
            auto [currentDist, u] = pq.top();
            pq.pop();

            if (u == des) return dist[des];
            if (currentDist > dist[u]) continue;

            for (auto& [v, cost] : adjCost[u]) {
                int newDist = dist[u] + cost;
                if (newDist < dist[v]) {
                    dist[v] = newDist;
                    parent[v] = u;
                    pq.emplace(newDist, v);
                }
            }
        }

        return dist[des] == INT_MAX ? -1 : dist[des];
    }

    // Dijkstra's algorithm for minimum time path
    int dijkstraTime(int src, int des, vector<int>& parent) {
        int n = stations.size();
        vector<int> time(n, INT_MAX);
        priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> pq;

        time[src] = 0;
        parent[src] = src;
        pq.emplace(0, src);

        while (!pq.empty()) {
            auto [currentTime, u] = pq.top();
            pq.pop();

            if (u == des) return time[des];
            if (currentTime > time[u]) continue;

            for (auto& [v, t] : adjTime[u]) {
                int newTime = time[u] + getTimeWithTraffic(u, v);
                if (newTime < time[v]) {
                    time[v] = newTime;
                    parent[v] = u;
                    pq.emplace(newTime, v);
                }
            }
        }

        return time[des] == INT_MAX ? -1 : time[des];
    }


    // Floyd-Warshall algorithm for all pairs shortest paths
    void precomputeAllPairs() {
        int n = stations.size();
        allPairsCost = costMatrix;
        allPairsTime = timeMatrix;
        nextHopCost.resize(n, vector<int>(n, -1));
        nextHopTime.resize(n, vector<int>(n, -1));

        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                if (i != j && allPairsCost[i][j] != INT_MAX) {
                    nextHopCost[i][j] = j;
                }
                if (i != j && allPairsTime[i][j] != INT_MAX) {
                    nextHopTime[i][j] = j;
                }
            }
        }

        for (int k = 0; k < n; ++k) {
            for (int i = 0; i < n; ++i) {
                for (int j = 0; j < n; ++j) {
                    if (allPairsCost[i][k] != INT_MAX && allPairsCost[k][j] != INT_MAX &&
                        allPairsCost[i][j] > allPairsCost[i][k] + allPairsCost[k][j]) {
                        allPairsCost[i][j] = allPairsCost[i][k] + allPairsCost[k][j];
                        nextHopCost[i][j] = nextHopCost[i][k];
                    }

                    if (allPairsTime[i][k] != INT_MAX && allPairsTime[k][j] != INT_MAX &&
                        allPairsTime[i][j] > allPairsTime[i][k] + allPairsTime[k][j]) {
                        allPairsTime[i][j] = allPairsTime[i][k] + allPairsTime[k][j];
                        nextHopTime[i][j] = nextHopTime[i][k];
                    }
                }
            }
        }

        precomputedAllPairs = true;
    }

    // Get precomputed shortest path (must call precomputeAllPairs first)
    int getAllPairsCost(int src, int des, vector<int>& path) {
        if (!precomputedAllPairs) {
            cerr << "Must call precomputeAllPairs() first!" << endl;
            return -1;
        }

        if (allPairsCost[src][des] == INT_MAX) return -1;

        path.clear();
        int current = src;
        while (current != des) {
            path.push_back(current);
            current = nextHopCost[current][des];
            if (current == -1) return -1;
        }
        path.push_back(des);

        return allPairsCost[src][des];
    }



    // Greedy Best-First Search
    int greedyBFS(int src, int des, vector<int>& parent) {
        int n = stations.size();
        vector<bool> visited(n, false);
        auto cmp = [&](pair<int, int> a, pair<int, int> b) {
            return heuristic(a.first, des) > heuristic(b.first, des);
        };
        priority_queue<pair<int, int>, vector<pair<int, int>>, decltype(cmp)> pq(cmp);

        pq.emplace(src, 0);
        visited[src] = true;
        parent[src] = src;

        while (!pq.empty()) {
            auto [u, cost] = pq.top();
            pq.pop();

            if (u == des) return cost;

            for (auto& [v, c] : adjCost[u]) {
                if (!visited[v]) {
                    visited[v] = true;
                    parent[v] = u;
                    pq.emplace(v, cost + c);
                }
            }
        }

        return -1;
    }

    // Dynamic Programming approach with limited stops
    int dpLimitedStops(int src, int des, int maxStops, vector<int>& path) {
        int n = stations.size();
        vector<vector<int>> dp(maxStops + 1, vector<int>(n, INT_MAX));
        vector<vector<int>> parentStop(maxStops + 1, vector<int>(n, -1));

        dp[0][src] = 0;

        for (int stops = 1; stops <= maxStops; ++stops) {
            for (int u = 0; u < n; ++u) {
                dp[stops][u] = dp[stops-1][u];
                parentStop[stops][u] = parentStop[stops-1][u];

                for (auto& [v, cost] : adjCost[u]) {
                    if (dp[stops-1][v] != INT_MAX && dp[stops][u] > dp[stops-1][v] + cost) {
                        dp[stops][u] = dp[stops-1][v] + cost;
                        parentStop[stops][u] = v;
                    }
                }
            }
        }

        if (dp[maxStops][des] == INT_MAX) return -1;

        // Reconstruct path
        path.clear();
        int current = des;
        int stops = maxStops;
        while (current != src && stops >= 0) {
            path.push_back(current);
            current = parentStop[stops][current];
            stops--;
        }
        path.push_back(src);
        reverse(path.begin(), path.end());

        return dp[maxStops][des];
    }

    // Multi-criteria optimization (Pareto optimal)
    vector<pair<int, int>> multiCriteriaOptimization(int src, int des) {
        int n = stations.size();
        vector<set<pair<int, int>>> pareto(n); // {cost, time}

        auto cmp = [](const pair<int, int>& a, const pair<int, int>& b) {
            return a.first + a.second < b.first + b.second;
        };
        priority_queue<pair<int, int>, vector<pair<int, int>>, decltype(cmp)> pq(cmp);

        pareto[src].insert({0, 0});
        pq.emplace(0, src);

        while (!pq.empty()) {
            auto [currentCost, u] = pq.top();
            pq.pop();

            for (auto& [v, cost] : adjCost[u]) {
                for (auto& [c, t] : pareto[u]) {
                    int newCost = c + cost;
                    int newTime = t + getTimeWithTraffic(u, v);

                    bool dominated = false;
                    for (auto it = pareto[v].begin(); it != pareto[v].end(); ) {
                        if (it->first <= newCost && it->second <= newTime) {
                            dominated = true;
                            break;
                        }
                        if (it->first >= newCost && it->second >= newTime) {
                            it = pareto[v].erase(it);
                        } else {
                            ++it;
                        }
                    }

                    if (!dominated) {
                        pareto[v].insert({newCost, newTime});
                        pq.emplace(newCost, v);
                    }
                }
            }
        }

        vector<pair<int, int>> results(pareto[des].begin(), pareto[des].end());
        return results;
    }

    // ==================== Additional Features ====================

    // Add traffic delay to an edge
    void addTraffic(int u, int v, int delay) {
        trafficUpdates[u].emplace_back(v, delay);
        trafficUpdates[v].emplace_back(u, delay);
    }

    // Check if two stations are connected
    bool areConnected(int u, int v) {
        return dsu.isConnected(u, v);
    }

    // Autocomplete station names
    vector<string> autocomplete(const string& prefix) {
        auto results = trie.searchPrefix(prefix);
        vector<string> names;
        for (auto& [name, index] : results) {
            names.push_back(name);
        }
        return names;
    }

    // Save favorite route for a user
    void saveFavoriteRoute(const string& username, const vector<int>& path, int criteria) {
        favoriteRoutes[username].emplace_back(path, criteria);
    }

    // Get favorite routes for a user
    vector<pair<vector<int>, int>> getFavoriteRoutes(const string& username) {
        return favoriteRoutes[username];
    }

    // Print path
    void printPath(const vector<int>& path) {
        for (int i = 0; i < path.size(); ++i) {
            cout << stations[path[i]];
            if (i != path.size() - 1) cout << " -> ";
        }
        cout << endl;
    }

    // Get all stations
    const vector<string>& getAllStations() const {
        return stations;
    }

    // Load data from file
    void loadFromFile(const string& filename) {
        ifstream file(filename);
        if (!file.is_open()) {
            cerr << "Failed to open file: " << filename << endl;
            return;
        }

        string line;
        while (getline(file, line)) {
            stringstream ss(line);
            int u, v, cost, time;
            if (ss >> u >> v >> cost >> time) {
                // Add the path to the system
                adjCost[u].emplace_back(v, cost);
                adjCost[v].emplace_back(u, cost);
                adjTime[u].emplace_back(v, time);
                adjTime[v].emplace_back(u, time);

                costMatrix[u][v] = costMatrix[v][u] = cost;
                timeMatrix[u][v] = timeMatrix[v][u] = time;

                dsu.unionSets(u, v);
            }
        }
        file.close();
    }
};

// ==================== User Interface Functions ====================

void displayMainMenu() {
    cout << "\n===== SMART ROUTE PLANNER =====\n";
    cout << "1. Find Route\n";
    cout << "2. View Favorite Routes\n";
    cout << "3. Simulate Traffic\n";
    cout << "4. Check Station Connectivity\n";
    cout << "5. Autocomplete Station Names\n";
    cout << "6. Exit\n";
    cout << "Enter your choice: ";
}

void displayRouteMenu() {
    cout << "\n===== ROUTE OPTIONS =====\n";
    cout << "1. Minimum Cost (Dijkstra)\n";
    cout << "2. Minimum Time (Dijkstra)\n";
    cout << "3. Multi-criteria Optimal Paths\n";
    cout << "4. Path with Limited Stops\n";
    cout << "5. Use Greedy BFS (fast but approximate)\n";
    cout << "6. Back to Main Menu\n";
    cout << "Enter your choice: ";
}

int getStationIndex(const vector<string>& stations, const string& name) {
    for (int i = 0; i < stations.size(); ++i) {
        if (stations[i] == name) return i;
    }
    return -1;
}

void findRoute(RoutePlanner& planner, const string& username) {
    vector<string> stations = planner.getAllStations();
    string srcName, desName;

    cout << "\nAvailable Stations:\n";
    for (int i = 0; i < stations.size(); ++i) {
        cout << i << ". " << stations[i] << "\n";
    }

    cout << "Enter source station name: ";
    cin >> srcName;
    cout << "Enter destination station name: ";
    cin >> desName;

    int src = getStationIndex(stations, srcName);
    int des = getStationIndex(stations, desName);

    if (src == -1 || des == -1) {
        cout << "Invalid station names!\n";
        return;
    }

    int routeChoice;
    do {
        displayRouteMenu();
        cin >> routeChoice;

        vector<int> parent(stations.size(), -1);
        vector<int> path;
        int result;

        switch (routeChoice) {
            case 1: {
                result = planner.dijkstraCost(src, des, parent);
                if (result == -1) {
                    cout << "No path exists!\n";
                } else {
                    cout << "\nMinimum cost: " << result << " Rs.\n";
                    cout << "Path: ";
                    int current = des;
                    while (current != src) {
                        path.push_back(current);
                        current = parent[current];
                    }
                    path.push_back(src);
                    reverse(path.begin(), path.end());
                    planner.printPath(path);

                    // Option to save as favorite
                    cout << "Save as favorite? (y/n): ";
                    char choice;
                    cin >> choice;
                    if (choice == 'y' || choice == 'Y') {
                        planner.saveFavoriteRoute(username, path, 0); // 0 for cost
                        cout << "Route saved to favorites!\n";
                    }
                }
                break;
            }

            case 2: {
                result = planner.dijkstraTime(src, des, parent);
                if (result == -1) {
                    cout << "No path exists!\n";
                } else {
                    cout << "\nMinimum time: " << result << " minutes\n";
                    cout << "Path: ";
                    int current = des;
                    while (current != src) {
                        path.push_back(current);
                        current = parent[current];
                    }
                    path.push_back(src);
                    reverse(path.begin(), path.end());
                    planner.printPath(path);

                    // Option to save as favorite
                    cout << "Save as favorite? (y/n): ";
                    char choice;
                    cin >> choice;
                    if (choice == 'y' || choice == 'Y') {
                        planner.saveFavoriteRoute(username, path, 1); // 1 for time
                        cout << "Route saved to favorites!\n";
                    }
                }
                break;
            }

            case 3: {
                auto results = planner.multiCriteriaOptimization(src, des);
                if (results.empty()) {
                    cout << "No path exists!\n";
                } else {
                    cout << "\nPareto optimal paths (cost, time):\n";
                    for (auto& [cost, time] : results) {
                        cout << "Cost: " << cost << " Rs., Time: " << time << " min\n";
                    }
                }
                break;
            }

            case 4: {
                int maxStops;
                cout << "Enter maximum number of stops: ";
                cin >> maxStops;

                result = planner.dpLimitedStops(src, des, maxStops, path);
                if (result == -1) {
                    cout << "No path exists with " << maxStops << " stops or fewer!\n";
                } else {
                    cout << "\nMinimum cost with " << maxStops << " stops: " << result << " Rs.\n";
                    cout << "Path: ";
                    planner.printPath(path);
                }
                break;
            }


            case 5: {
                result = planner.greedyBFS(src, des, parent);
                if (result == -1) {
                    cout << "No path exists!\n";
                } else {
                    cout << "\nApproximate cost (Greedy BFS): " << result << " Rs.\n";
                    cout << "Path: ";
                    int current = des;
                    while (current != src) {
                        path.push_back(current);
                        current = parent[current];
                    }
                    path.push_back(src);
                    reverse(path.begin(), path.end());
                    planner.printPath(path);
                }
                break;
            }

            case 6:
                break;

            default:
                cout << "Invalid choice!\n";
        }

        if (routeChoice != 6) {
            cout << "\nPress Enter to continue...";
            cin.ignore();
            cin.get();
        }
    } while (routeChoice != 6);
}

void viewFavoriteRoutes(RoutePlanner& planner, const string& username) {
    auto favorites = planner.getFavoriteRoutes(username);

    if (favorites.empty()) {
        cout << "\nNo favorite routes saved!\n";
        return;
    }

    cout << "\n===== FAVORITE ROUTES =====\n";
    for (int i = 0; i < favorites.size(); ++i) {
        cout << i+1 << ". ";
        if (favorites[i].second == 0) {
            cout << "[Minimum Cost] ";
        } else {
            cout << "[Minimum Time] ";
        }
        planner.printPath(favorites[i].first);
    }

    cout << "\nPress Enter to continue...";
    cin.ignore();
    cin.get();
}

void simulateTraffic(RoutePlanner& planner) {
    cout << "\n=== TRAFFIC SIMULATION ===\n";
    auto stations = planner.getAllStations();
    for (int i = 0; i < stations.size(); ++i) {
        cout << i << ". " << stations[i] << "\n";
    }

    int u, v, delay;
    cout << "Enter start station index: ";
    cin >> u;
    cout << "Enter end station index: ";
    cin >> v;
    cout << "Enter delay in minutes: ";
    cin >> delay;

    planner.addTraffic(u, v, delay);
    cout << "Traffic delay added between " << stations[u] << " and " << stations[v] << "!\n";

    cout << "\nPress Enter to continue...";
    cin.ignore();
    cin.get();
}

void checkConnectivity(RoutePlanner& planner) {
    string station1, station2;
    cout << "\nEnter first station: ";
    cin >> station1;
    cout << "Enter second station: ";
    cin >> station2;

    auto stations = planner.getAllStations();
    int s1 = getStationIndex(stations, station1);
    int s2 = getStationIndex(stations, station2);

    if (s1 == -1 || s2 == -1) {
        cout << "Invalid station names!\n";
    } else if (planner.areConnected(s1, s2)) {
        cout << station1 << " and " << station2 << " are connected!\n";
    } else {
        cout << station1 << " and " << station2 << " are NOT connected!\n";
    }

    cout << "\nPress Enter to continue...";
    cin.ignore();
    cin.get();
}

void autocompleteDemo(RoutePlanner& planner) {
    string prefix;
    cout << "\nEnter station name prefix: ";
    cin >> prefix;

    auto suggestions = planner.autocomplete(prefix);
    if (suggestions.empty()) {
        cout << "No stations found with that prefix!\n";
    } else {
        cout << "Suggestions:\n";
        for (auto& name : suggestions) {
            cout << "- " << name << "\n";
        }
    }

    cout << "\nPress Enter to continue...";
    cin.ignore();
    cin.get();
}

// ==================== Main Function ====================

int main() {
    vector<string> stations = {
        "gitanjali", "netaji", "kalighat", "parkstreet", "mgroad",
        "shyambazar", "dumdum", "noapara", "baranagar", "dakshineswar"
    };

    // {u, v, cost, time}
    vector<vector<int>> paths = {
        {0,1,50,1}, {0,2,30,2}, {2,3,10,1}, {1,2,20,2}, {1,5,100,7},
        {1,3,50,3}, {2,4,20,4}, {2,6,100,5}, {3,4,30,2}, {3,5,30,3},
        {4,5,20,2}, {5,6,50,1}, {6,7,40,2}, {7,8,56,4}, {8,9,127,12},
        {6,8,99,5}, {6,9,256,14}, {3,7,80,9}, {4,8,185,7}, {2,9,360,20}
    };

    RoutePlanner planner(stations, paths);
    planner.precomputeAllPairs();

    // Load additional data from file if available
    planner.loadFromFile("additional_routes.txt");

    cout << "===== WELCOME TO SMART ROUTE PLANNER =====\n";
    cout << "Enter your username: ";
    string username;
    cin >> username;

    int choice;
    do {
        displayMainMenu();
        cin >> choice;

        switch (choice) {
            case 1:
                findRoute(planner, username);
                break;

            case 2:
                viewFavoriteRoutes(planner, username);
                break;

            case 3:
                simulateTraffic(planner);
                break;

            case 4:
                checkConnectivity(planner);
                break;

            case 5:
                autocompleteDemo(planner);
                break;

            case 6:
                cout << "Exiting...\n";
                break;

            default:
                cout << "Invalid choice!\n";
        }

    } while (choice != 6);

    return 0;
}
