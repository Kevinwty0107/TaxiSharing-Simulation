#include <stdio.h>
#include <time.h>
#include "CityMapFloat.hpp"
#include "KdTrip.hpp"
#include <boost/date_time/gregorian/gregorian_types.hpp>

#define MN_COUNT 10819

using namespace std;
struct Edge {
  int src, dst;
  float distance;

  Edge(int s, int d, float l): src(s), dst(d), distance(l) {}

  bool operator<(const Edge &e) const {
    return ((this->dst<e.dst) || (this->dst==e.dst && this->distance<e.distance) ||
            (this->dst==e.dst && this->distance==e.distance && this->src<e.src));
  }
};

int main(int argc, char **argv)
{
  if (argc<3) {
    fprintf(stderr, 
            "Usage: %s  <IN_TAXI_TRIP_RECORDS_FILE> <FULL_CITY_MAP>\n", 
            argv[0]);
    return -1;
  }
  boost::iostreams::mapped_file mfile(std::string(argv[1]),
                                      boost::iostreams::mapped_file::priv);
  int nTrip = mfile.size()/sizeof(KdTrip::Trip);
  KdTrip::Trip *trips = (KdTrip::Trip*)mfile.const_data();
  CityMap *city = new CityMap(argv[2]);

  std::vector<int> counts(city->numIntersections(), 0);
  
  for (int i=0; i<nTrip; ++i, ++trips) {
    int src = city->mapToIntersection(CityMap::Location(trips->pickup_lat, trips->pickup_long));
    int dst = city->mapToIntersection(CityMap::Location(trips->dropoff_lat, trips->dropoff_long));
    if (src!=-1 && dst!=-1) {
      ++counts[src];
      ++counts[dst];
    }
  }

  float bounds[3][4] = {
    {40.7649, -73.8896, 40.7875, -73.8513}, // LGA
    {40.6195, -73.8352, 40.6659, -73.7401}  // JFK
  };

  int nodeCount = MN_COUNT;
  std::vector<Edge> finalEdges;
  std::vector<int> finalNodes;
  for (int ap=0; ap<2; ++ap) {
    std::vector<int> airports;
    for (int i=0; i<city->numIntersections(); ++i) {
      const CityMap::Location &loc = city->getIntersection(i);
      if (counts[i]>100 && loc.lat>bounds[ap][0] && loc.lat<bounds[ap][2] && loc.lon>bounds[ap][1] && loc.lon<bounds[ap][3]) {
        airports.push_back(i);
        // fprintf(stderr, "%2d: %d -- %.6lf,%.6lf\n", i, counts[i], loc.lat, loc.lon);
      }
    }

    fprintf(stderr, "Airport Intersections: %d\n", (int)airports.size());

    // Find and validate shortest paths
    std::vector<int> vPrev(city->numIntersections());
    std::vector<float> vDist(city->numIntersections());
    std::vector<Edge> edges;
    for (int i=0; i<airports.size(); ++i) {
      int *prev = &vPrev[0];
      float *dist = &vDist[0];
      city->shortestPaths(airports[i], prev, dist);
      for (int u=0; u<MN_COUNT; ++u) {
        if (prev[u]>=MN_COUNT) {
          edges.push_back(Edge(airports[i], u, dist[u]));
        }
      }
    }

    std::set<int> nodeSet;
    std::vector<int> nodes;

    std::sort(edges.begin(), edges.end());

    fprintf(stderr, "New edges: %d\n", (int)edges.size()*2);
    int lastV = -1;
    int order = 0;
    for (int i=0; i<edges.size(); ++i) {
      int u = edges[i].src;
      int v = edges[i].dst;
      // fprintf(stderr, "Edge %d: (%d,%d,%.3f)\n", i, u, v, edges[i].distance);
      if (v==lastV) {
        edges[i].dst = edges[i-1].src;
        if (nodeSet.find(edges[i].src)==nodeSet.end()) {
          nodes.push_back(edges[i].src);
          nodeSet.insert(edges[i].src);
        }
      }
      else {
        nodes.clear();
        nodeSet.clear();
        finalEdges.push_back(Edge(nodeCount, edges[i].dst, edges[i].distance));
        nodes.push_back(edges[i].src);
        nodeSet.insert(edges[i].src);
      }
      lastV = v;
    }
    for (int i=0; i<airports.size(); ++i) {
      if (nodeSet.find(airports[i])==nodeSet.end()) {
        nodeSet.insert(airports[i]);
        nodes.push_back(airports[i]);
      }
    }
    for (int i=1; i<nodes.size(); ++i) {
      finalEdges.push_back(Edge(nodeCount+i, nodeCount+i-1, CityMap::distance(city->getIntersection(nodes[i]),
                                                                              city->getIntersection(nodes[i-1]))));
    }
    // for (int i=0; i<finalEdges.size(); ++i) {
    //   fprintf(stderr, "ADD: %d %d %.3f\n", finalEdges[i].src, finalEdges[i].dst, finalEdges[i].distance);
    // }
    nodeCount += nodes.size();
    finalNodes.insert(finalNodes.end(), nodes.begin(), nodes.end());
  }
  std::vector<CityMap::Street> streets;
  for (int i=0; i<city->numStreets(); ++i) {
    const CityMap::Street &s = city->getStreet(i);
    if (s.first<MN_COUNT && s.second<MN_COUNT)
      streets.push_back(s);
  }
  fprintf(stdout, "%d %d\n", nodeCount, (int)(streets.size()+finalEdges.size()*2));
  for (int i=0; i<MN_COUNT; ++i)
    fprintf(stdout, "%.6lf %.6lf\n", city->getIntersection(i).lat, city->getIntersection(i).lon);
  for (int i=0; i<finalNodes.size(); ++i)
    fprintf(stdout, "%.6lf %.6lf\n", city->getIntersection(finalNodes[i]).lat, city->getIntersection(finalNodes[i]).lon); 
 
  for (int i=0; i<streets.size(); ++i)
    fprintf(stdout, "%d %d %.3f\n", streets[i].first, streets[i].second, city->getStreetWeight(streets[i]));
  for (int i=0; i<finalEdges.size(); ++i) {
    fprintf(stdout, "%d %d %.3f\n", finalEdges[i].src, finalEdges[i].dst, finalEdges[i].distance);
    fprintf(stdout, "%d %d %.3f\n", finalEdges[i].dst, finalEdges[i].src, finalEdges[i].distance);
  }
  fprintf(stderr, "Added %d nodes and %d edges\n", (int)finalNodes.size(), (int)finalEdges.size()*2);
  return 0;
}
