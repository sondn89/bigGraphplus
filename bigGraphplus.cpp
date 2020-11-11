#include <string.h>
#include <vector>
#include <cstdlib>
#include <cstdio>
#include <tuple>
#include <cassert>
#include <iostream>
#include <algorithm>
#include <stack>
#include <queue>
#include <tuple>
#include <map>
#include <stdint.h>
#include <cassert>
#include <cstdlib>
#include <iomanip>
#include <cilk/cilk_api.h>
#include <cilk/cilk.h>

#include "creducer_opadd_array.h" 
#include "CycleTimer.h"

#define OUTGOING 0
#define INCOMING 1

using namespace std;
using namespace cilk;

template <typename T> class VQueue {	
size_t V;
size_t curr_;
size_t next_;
size_t end_;

public:
	vector<T> data;vector<T> value;
	explicit VQueue(size_t V) : data(V), value(V), V(V), curr_(0), next_(0), end_(0){
	}
  // virtual ~VQueue(){ delete [] data; }
	inline bool empty() const { return curr_ == next_; }
	inline bool full() const { return end_ == V; }
	inline T &front() { return data[curr_];}
	inline size_t size() const { return end_; }
	inline void pop() { ++curr_; assert(curr_ <= end_);}
	inline void push(const T &val){ data[end_++] = val; assert(end_ <= V);}
	inline void push(const T &node, const T &val){ data[end_] = node;value[end_++] = val; assert(end_ <= V);}
	inline void next() {  assert(curr_ == next_);next_ = end_; }//
	inline void clear() { curr_ = next_ = end_ = 0; }
	inline void resize(size_t V_){
		if (V_ > V){ V = V_; data.resize(V); value.resize(V);}
	}
	inline size_t sum(){
		size_t s=0;
		for (uint32_t i = 0; i < end_; i++){
			s += value[i];
		}
		return s;
	}

	inline typename vector<T>::iterator begin() { return data.begin();}
	inline typename vector<T>::iterator end() { return data.begin() + end_;}
};

const uint32_t ALIVE   = 0;
const uint32_t DEAD    = 1;
const uint32_t UNKNOWN = 2;
const uint32_t MASK    = 3;

//tbb::concurrent_
vector<tuple<uint32_t, uint32_t, uint32_t, char> > 	updates; // <source, target, timestamp, type>
vector<tuple<uint32_t, uint32_t, uint32_t> > 		queries; // <source, target, timestamp>
map<uint32_t, uint32_t> nodeMapping; // mapping of input node-identifiers to 0, .., n-1
map<uint32_t, uint32_t> revMapping; // mapping 0, .., n-1 to input node-identifiers 
vector<vector<uint32_t>>			Edges;
vector<vector<uint32_t>>			Maps;//for all threads
vector<VQueue<uint32_t> > 			Queues;//for all threads
vector<int>							Distances;//for all nodes
uint32_t  							nodeNum = 0, edgeNum=0, nextV = 0;
bool 								diGraph = false, verbose = false;
uint32_t 							testNum = 1;
uint32_t 							threadNum = __cilkrts_get_nworkers();


static inline uint32_t GetID(uint32_t v) { return v >> 2; }
static inline uint32_t GetState(uint32_t v)  { return v & MASK; }
static inline uint32_t ToEdge(uint32_t v) { return (v << 2) ;} //| ALIVE
static inline void ResetMap(uint32_t threadID)
{
	for (uint32_t v : Queues[threadID].data) {
		Maps[threadID][v>>5] = 0;
	}
}
//set bit at v in Maps
static inline void SetBit(uint32_t threadID, uint32_t v)
{
	Maps[threadID][v >> 5] |= (1 << ( v & 31 ));
}

//test bit at v in Maps
static inline int TestBit(uint32_t threadID, uint32_t v)
{
	return (Maps[threadID][v >> 5] >> (v & 31) ) & 1;
}

// map input file node node number to id in range [0,n-1]
static inline uint32_t MapNode(const uint32_t v) {
    if(nodeMapping.find(v) == nodeMapping.end()) {
        nodeMapping[v] = nextV;
        revMapping[nextV] = v;
        nextV++;
    } 
    return nodeMapping[v];
} // mapNode

// reverse map node id to original node number
static inline uint32_t NodeMap(const uint32_t n) {
    return revMapping[n];
} // NodeMap


inline bool readeof() {
	for (;;) {
		int c = getc_unlocked(stdin);
		if (c == EOF || c == '#') {
			return true;
		} else if (isspace(c)) {
			continue;
		} else {
			ungetc(c, stdin);
			return false;
		}
	}
	assert(false);
}

inline uint32_t readuint() {
	uint32_t c;
	uint32_t x;
	while (!isdigit(c = getc_unlocked(stdin)));
	x = c - '0';
	while (isdigit(c = getc_unlocked(stdin))) {
		x = (x * 10 + (c - '0'));
	}
	return x;
}

void Debug(char * msg, vector<uint32_t> v) {
	cout << endl << msg << " - Debug [ ";
	for (uint32_t i = 0; i < v.size(); i++) {
		cout << v[i] << " ";
	}
	cout << "]" << endl;
}

void Dump() {
        cout << endl;
        for (uint32_t i = 0; i < Edges.size(); i++) {
                cout << i << " -> [ ";
                for (uint32_t y = 0; y < Edges[i].size(); y++) {
                        cout << Edges[i][y] << " ";
                }
                cout << "]" << endl;
        }
}

void Build(char * filename)
{
	cerr << "Building the big graph..." ;
	nodeMapping.clear();
    revMapping.clear();
    //1.fetch edge set from stdin  
	FILE *fp = stdin; size_t bufsize=0;char *line = NULL;
	fp = fopen(filename,"r");
	int res; uint32_t u, v;
	Edges.clear(); 
	Edges.resize(1e7);

    // vertex identified from 0 -> n
	while (!feof(fp)){
		res = getline(&line,&bufsize,fp);
		if (res == -1) break;
		if (line[0] == 'S') break;

		res = sscanf(line, "%u %u", &u, &v);
		if ( !res || res == EOF ) {
			continue;
		} 
		u = MapNode(u); v = MapNode(v);
		nodeNum = max({nodeNum, u + 1, v + 1});  
		if (nodeNum>Edges.size()){
			Edges.resize(nodeNum + 1e6); 
		}

		Edges[u].push_back(v);
		if (!diGraph) Edges[v].push_back(u); 
	}
	fclose(fp);
	cerr << " Done.";
	//nodeNum += 1e5;//add more nodes 
        //cerr << "End of init" << endl;
	Edges.resize(nodeNum);
	edgeNum = 0;

        //sort adjacent lists
        uint32_t nZero = 0, nOne=0; 	 
	vector<uint32_t> Degree1Nodes;
	Degree1Nodes.resize(1e7);
	uint32_t Removed = 0;
	vector<tuple<uint32_t, uint32_t>> ToBeRemoved;
	
	//for (uint32_t x = 0; x < Edges.size(); x++) {
	//	for (uint32_t y = 0; y < Edges[x].size(); y++) {
	//		cout << x << "           " << Edges[x][y] << endl;
	//	}
	//}

	for (uint32_t v = 0; v < nodeNum; v++){
		//cout << endl << "Processing " << v << " --> [";
		
		//for (uint32_t x = 0; x < Edges[v].size(); x++) {
		//	cout << Edges[v][x] << " ";
		//}
		//cout << "]" << endl;

		sort(Edges[v].begin(), Edges[v].end());
		Edges[v].erase(unique(Edges[v].begin(), Edges[v].end()), Edges[v].end());

		edgeNum += Edges[v].size();
		if (Edges[v].size() ==0) ++nZero;
		else if (Edges[v].size() ==1) ++nOne;
		
		if (Edges[v].size() == 1) {
			if (count(Degree1Nodes.begin(), Degree1Nodes.end(), Edges[v][0])) {
				ToBeRemoved.push_back(make_tuple(v, Edges[v][0]));
				edgeNum = edgeNum - 2;
				nOne--;
			} else {
				// cout << "Solo node found " << v << endl;
				Degree1Nodes.push_back(Edges[v][0]);
			}
		} else {
			// cout << v << " has mulitple edges" << endl;
		}
	}

	// Dump();

	// Removing those removable nodes
	for (uint32_t i = 0; i < ToBeRemoved.size(); i++) {
		tuple<uint32_t, uint32_t> t = ToBeRemoved[i];
		// cout << "Removing " << "[ " << get<0>(t) << " " << get<1>(t) << " ]" << endl;
	
		uint32_t removeInEdge = get<0>(t);
		Edges[removeInEdge].erase(Edges[removeInEdge].begin(), Edges[removeInEdge].end());		
		
		uint32_t removeInEdgeVector = get<1>(t);
		Edges[removeInEdgeVector].erase(remove(Edges[removeInEdgeVector].begin(), Edges[removeInEdgeVector].end(), removeInEdge), Edges[removeInEdgeVector].end());
		Removed++;
	}	
	// Dump();

	// Edges.resize(nodeNum);	

	edgeNum = (diGraph?edgeNum : edgeNum/2);
    //2. Init the graph
	Queues.clear();
	Maps.clear();
	for (uint32_t t = 0; t < threadNum; t++){
		Queues.emplace_back(VQueue<uint32_t>(nodeNum));
		Maps.emplace_back(vector<uint32_t>(nodeNum /32 + 1) );    	
	}
	Distances.resize(nodeNum);

	cerr << " Num of nodes " << nodeNum << "(" << nZero << " isolated nodes, " << nOne <<" degree-1 nodes, " << Removed << " turned isolated), num of edges " << edgeNum << endl;
}

//Compute in parallel the Betweenness Centrality for all nodes
void computeBC()
{
	double BC[nodeNum];
	for (int i=0; i< testNum; i++)
	{
		std::fill_n(BC, nodeNum, 0);
		double start = CycleTimer::currentSeconds();
		cilkpub::creducer_opadd_array<double> rBC(BC, nodeNum) ;
		cilk_for(uint32_t s=0; s< nodeNum; s++){
			//if ((Edges[s].size() > 0)) //{	rBC[s] = 0.0;} else //|| (Edges[s].size() == 1)
			{
				vector<vector<uint32_t>> Pred(nodeNum);
				vector<int> dist(nodeNum,-1), sigma(nodeNum,0);
				vector<double> delta(nodeNum,0.0);
				stack<uint32_t> S;
				queue<uint32_t> Q;

				//init 
				dist[s]	= 0; sigma[s] = 1; Q.push(s);
				//SSSP
				while (!Q.empty()) {		
					uint32_t v = Q.front();Q.pop();
			
					S.push(v);
					for (uint32_t w : Edges[v]) {
						if (dist[w] == -1){ //w found for the first time
							dist[w] = dist[v] + 1;
							Q.push(w);
						}
						//path counting
						if (dist[w] == (dist[v]+1)){
							sigma[w] += sigma[v];
							Pred[w].push_back(v);
						}
					}
				}
				//Accumulation
				while(!S.empty()) {
					uint32_t w = S.top();S.pop();
					for (uint32_t v: Pred[w]) {
						delta[v] += (1+delta[w])*sigma[v]/sigma[w];			
					}
					if (w != s) {
						rBC[w] += delta[w];
					}
				}
			}
		}
		rBC.move_out(BC);
		cout << CycleTimer::currentSeconds() - start << " s" << endl;
	}	
	cilk_for (int i = 0; i < nodeNum; i++) if(diGraph) BC[i] = BC[i]/2;
	if (verbose) {
		for (int i = 0; i < nodeNum; i++) cout << NodeMap(i) << " " << BC[i] << endl;
    }	

}
//Compute in serial the Betweenness Centrality for all nodes
void computeBCserial()
{
	double BC[nodeNum];	
	for (int i=0; i< testNum; i++)
	{
		std::fill_n(BC, nodeNum, 0);
		double start = CycleTimer::currentSeconds();
		for(uint32_t s=0; s< nodeNum; s++){
			vector<vector<uint32_t>> Pred(nodeNum);
			vector<int> dist(nodeNum,-1), sigma(nodeNum,0);
			vector<double> delta(nodeNum,0.0);
			stack<uint32_t> S;
			queue<uint32_t> Q;

			//init 
			dist[s]	= 0; sigma[s] = 1; Q.push(s);
			//SSSP
			while (!Q.empty()) {		
				uint32_t v = Q.front();Q.pop();		
				S.push(v);
				for (uint32_t w : Edges[v]) {
					if (dist[w] == -1){ //w found for the first time
						dist[w] = dist[v] + 1;
						Q.push(w);
					}
					//path counting
					if (dist[w] == (dist[v]+1)){
						sigma[w] += sigma[v];
						Pred[w].push_back(v);
					}
				}
			}
			//Accumulation
			while(!S.empty()) {
				uint32_t w = S.top();S.pop();
				for (uint32_t v: Pred[w]) {
					delta[v] += (1+delta[w])*sigma[v]/sigma[w];			
				}
				if (w != s) {
					BC[w] += delta[w];
				}
			}
		}
		cout << CycleTimer::currentSeconds() - start << " s" << endl;
	}	
	cilk_for (int i = 0; i < nodeNum; i++) if(diGraph) BC[i] = BC[i]/2;
	if (verbose) {
		for (int i = 0; i < nodeNum; i++) cout << i << " " << BC[i] << endl;
    }		
}
//Compute in parallel the Betweenness Centrality for all nodes
void TestComputeBC()
{
	vector<string> workers;
	workers = {"1", "2", "4", "8", "16", "32", "36"}	;

	double BC[nodeNum];	
	for (string nWorkers : workers)
	{
		std::fill_n(BC, nodeNum, 0);
		__cilkrts_end_cilk(); 
		__cilkrts_set_param("nworkers", nWorkers.c_str());
		double start = CycleTimer::currentSeconds();
		cilkpub::creducer_opadd_array<double> rBC(BC, nodeNum) ;
		cilk_for(uint32_t s=0; s< nodeNum; s++){
			vector<vector<uint32_t>> Pred(nodeNum);
			vector<int> dist(nodeNum,-1), sigma(nodeNum,0);
			vector<double> delta(nodeNum,0.0);
			stack<uint32_t> S;
			queue<uint32_t> Q;

			//init 
			dist[s]	= 0; sigma[s] = 1; Q.push(s);
			//SSSP
			while (!Q.empty()) {		
				uint32_t v = Q.front();Q.pop();		
				S.push(v);
				for (uint32_t w : Edges[v]) {
					if (dist[w] == -1){ //w found for the first time
						dist[w] = dist[v] + 1;
						Q.push(w);
					}
					//path counting
					if (dist[w] == (dist[v]+1)){
						sigma[w] += sigma[v];
						Pred[w].push_back(v);
					}
				}
			}
			//Accumulation
			while(!S.empty()) {
				uint32_t w = S.top();S.pop();
				for (uint32_t v: Pred[w]) {
					delta[v] += (1+delta[w])*sigma[v]/sigma[w];			
				}
				if (w != s) {
					rBC[w] += delta[w];
				}
			}
		}
		rBC.move_out(BC);
		cout << nWorkers << " " << CycleTimer::currentSeconds() - start << " s" << endl;
	}	
	cilk_for (int i = 0; i < nodeNum; i++) if(diGraph) BC[i] = BC[i]/2;
	if (verbose) {
		for (int i = 0; i < nodeNum; i++) cout << i << " " << BC[i] << endl;
    }			
}
//Compute in parallel the Closeness Centrality for all nodes
void computeCC()
{
	//vector<tuple<uint32_t, int>> Distances(nodeNum);
	vector<double> CC(nodeNum);
	for (int i=0; i< testNum; i++)
	{
		double start = CycleTimer::currentSeconds();
		cilk_for (uint32_t v = 0; v < nodeNum; v++){
			uint32_t threadID = __cilkrts_get_worker_number();    
			//travel SSSP from v
			auto &Q = Queues[threadID];	
			uint32_t distance = 0;			
			Q.clear();
			Q.push(v,0);
			Q.next();
			SetBit(threadID, v);			
			while (!Q.empty()) {
				distance++;
				while (!Q.empty()) {
					uint32_t s = Q.front();
					Q.pop();		
					for (uint32_t w : Edges[s]) {
						if (TestBit(threadID,w)) {
							continue;
						}
						Q.push(w, distance);
						SetBit(threadID,w);				
					}			
				}
				Q.next();
			}	
			ResetMap(threadID);
			distance = Q.sum();
			if (distance==0) CC[v] = 0.0;	
			else  CC[v] = ((double)(nodeNum-1) / distance);
		}
		cout << CycleTimer::currentSeconds() - start << " s" << endl;
	}	
	//show results
	if (verbose){ 
		for (uint32_t v = 0; v < nodeNum; v++){
			cout << v << "=="<< std::setprecision(4) <<CC[v] << endl;
		}
	}	
}
//Compute in serial the Closeness Centrality for all nodes
void computeCCserial()
{
	//vector<tuple<uint32_t, int>> Distances(nodeNum);
	vector<double> CC(nodeNum);
	for (int i=0; i< testNum; i++)
	{
		double start = CycleTimer::currentSeconds();
		for (uint32_t v = 0; v < nodeNum; v++){
			uint32_t threadID = 0;    
			//travel SSSP from v
			auto &Q = Queues[threadID];	
			uint32_t distance = 0;			
			Q.clear();
			Q.push(v,0);
			Q.next();
			SetBit(threadID, v);			
			while (!Q.empty()) {
				distance++;
				while (!Q.empty()) {
					uint32_t s = Q.front();
					Q.pop();		
					for (uint32_t w : Edges[s]) {
						if (TestBit(threadID,w)) {
							continue;
						}
						Q.push(w, distance);
						SetBit(threadID,w);				
					}			
				}
				Q.next();
			}	
			ResetMap(threadID);
			distance = Q.sum();
			if (distance==0) CC[v] = 0.0;	
			else  CC[v] = ((double)(nodeNum-1) / distance);
		}
		cout << CycleTimer::currentSeconds() - start << " s" << endl;
	}	
	//show results
	if (verbose){ 
		for (uint32_t v = 0; v < nodeNum; v++){
			cout << v << "=="<< std::setprecision(4) <<CC[v] << endl;
		}
	}	
}

int main(int argc, char *argv[])
{
	if (argc < 3) {
		cout << "Check params: filename isDirected method verbose" << endl;
		return 0;
	}
	cout << "NumThread = " << threadNum << endl;
	diGraph = atoi(argv[2]);
	Build(argv[1]);
	auto method = std::string(argv[3]);  
	if (argc==5) verbose = atoi(argv[4]);
	
	if (method == "CC") {
		cout << "Evaluating CC in Parallel..." << endl;
		computeCC();				
	}else if (method == "SCC") {
		cout << "Evaluating CC in Serial ..." << endl;
		computeCC();				
	}
	 else if (method == "BC") {
		cout << "Evaluating BC in Parallel..." << endl;
		computeBC();		
	} else if (method == "SBC") {
		cout << "Evaluating BC in Serial..." << endl;
		computeBCserial();
	} else if (method == "W") {
		cout << "Evaluating BC in changing nWorkers..." << endl;
		TestComputeBC();
	}
	

	cout << "Done!" << endl;
	return 0;
}
