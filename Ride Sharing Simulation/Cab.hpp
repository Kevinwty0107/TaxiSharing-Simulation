#ifndef CAB_HPP
#define CAB_HPP

#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <deque>
#include "CityMap.hpp"
#include "CabTrip.hpp"

// default speed per second
#define DEFAULT_SPEED (15000000/3600)
#define MAX_DELAY_DISTANCE 1000000
#define MAX_EXTRA_DISTANCE 2000000

/*
 *Class for a cab
 */
class Cab
{
public:
  // A Stop is either a pickup, a dropoff or a destination that a taxi needs to go to
  struct Stop {
    int       intersection; // location of the stop
    int       passengers;   // the number of passenger - possitive: pickup, negative: dropoff, zero: just a waypoint
    int       distance;     // distance from the last stop to this stop
    int       max_extra;    // the maximum extra distance incurred for from all the stops after this stop
    int       max_delay;    // the maximum distance delayed to pick up after this stop
    int       dist_acc;     // the accumulate distance from this stop to the final stop
    int       occ;          // occupancy at this stop
    CabTrip * trip;         // pointing to the trip associated with this stop, or NULL if it's just a random destination
    Stop(): intersection(-1), passengers(0), distance(0), max_extra(0), max_delay(0), dist_acc(0), occ(0), trip(0) {}
    Stop(int i, int p, int d, int o, CabTrip *t): intersection(i), passengers(p), distance(d), max_extra(0), max_delay(0), 
						  dist_acc(0), occ(o), trip(t) {}
  };
  typedef  std::list<Stop>  StopList;
  StopList stops;        // Stops being served by the cab
  int      id;           // This is the (unique) id of the cab (medallion?)
  int      max_share;    // The maximum number of shared trips
  int      capacity;     // Capacity of the cab
  int      occupancy;    // Current occupancy of the cab, counting all of its destination
  int      cur_pos;      // The current position of the cab
  int      speed;        // Current speed
  int      odometer;     // The total distance travel for the cab throughout the simulation
  int      dist_revenue; // The total distance that the taxi traveled with some passengers
  int      dist_driven;  // The distance traveled from the previous stop (not necessary the same as cur_pos) towards the first stop
  int      last_update;  // The time of the last update_cab() call

  std::vector<int> pathIntersection; // intersections of the path towards the first stop, in reverse
  std::vector<int> pathDistance;     // accumalated distance of the path intersection, in reverse
  int              cur_index;        // the current index along the path given this traveled distance

  // Caching computation for finding shareable stops
  bool                     shareability_changed; // Whether the shareable stop should be recomputed
  std::pair<StopList::iterator, int> saved_stop; // The last saved stop

  struct ServingOrder
  {
    int pick;
    int drop;
    ServingOrder(int p=-1, int d=-1): pick(p), drop(d) {}
    void reset(int p=-1, int d=-1) { this->pick = p; this->drop = d; }
    bool isValid() { return this->pick>=0; }
  };
  
public:
  Cab(int num_share, int cap=4, int id=-1);
  void  set_max_share(int num_share);

public:
  virtual ~Cab() {}
  virtual int   update_cab(CityMap *city, int time);
  virtual int   cost_to_share(CityMap *city, const CabTrip *trip, ServingOrder *so);
  virtual void  add_trip(CityMap *city, CabTrip *trip, const ServingOrder &order);
  
protected:
  int   find_shareable_stop(StopList::iterator &skip_it, int passengers);
  void  advance_odometer(int distance);
  int   pop_stop(int distance);
  bool  gen_path(CityMap *city, int src, int dst);
  void  gen_stop(CityMap *city);
};

typedef std::vector<Cab> CabList;

inline Cab::Cab(int n, int cap, int m)
    : id(m), max_share(n), capacity(cap), occupancy(0), cur_pos(-1), speed(DEFAULT_SPEED),
      odometer(0), dist_revenue(0), dist_driven(0), last_update(-1),
      cur_index(-1), shareability_changed(true)
{
}

inline void Cab::set_max_share(int num_share)
{
  this->max_share = num_share;
  this->shareability_changed = true;
}

inline int Cab::update_cab(CityMap *city, int time)
{
  // If this is the first update ever, making it like we're not moving
  if (this->last_update<0)
    this->last_update = time;

  // Update the timestamps
  int time_passed = time - this->last_update;
  this->last_update = time;
  
  // if we are not moving, no need to update
  if (time_passed<=0 && this->cur_pos>0)
    return this->cur_pos;

  // if we don't have a position (aka we could pop up anywhere),
  // teleport the cab to the first stop and reset the traveled
  // distance to 0 if possible
  if (this->cur_pos<0 && !this->stops.empty())
    this->cur_pos = this->pop_stop(0);

  // Now update the actual distance traveled
  int distance = this->speed*time_passed;
  this->dist_driven += distance;

  // Eliminate all reachable stops within the traveled distance
  while (!this->stops.empty() && this->dist_driven>=this->stops.front().distance) {
    const int stop_distance = this->stops.front().distance;
    // if the cab is not hired, just drive back and forth
    if (this->stops.front().passengers==0) {
      this->dist_driven %= stop_distance;
      break;
    }
    // otherwise take out one stop at a time
    this->dist_driven -= stop_distance;
    this->advance_odometer(distance-this->dist_driven);
    distance = this->dist_driven;
    this->cur_pos = this->pop_stop(this->dist_driven);
  }
  this->advance_odometer(distance);

  // the cab has passed all stops or has no position, make a new one
  if (this->stops.empty()) {
    this->gen_stop(city);
  }

  // otherwise...
  if (this->cur_pos>=0) {
    // find the actual path if we haven't done so
    if (this->pathIntersection.empty())
      this->gen_path(city, this->cur_pos, this->stops.front().intersection);

    while (this->dist_driven>=this->pathDistance.at(this->cur_index)) {
      --this->cur_index;
    }
  }
  return this->cur_pos;
}

inline void Cab::advance_odometer(int distance)
{
  this->odometer += distance;
  if (this->occupancy)
    this->dist_revenue += distance;
}


// Take out the first stop (aka we have arrived!) and use "distance" as
// the initial dist_driven value
inline int Cab::pop_stop(int distance)
{  

  this->dist_driven = distance;
  
  if (this->stops.empty())
    return -1;

  this->shareability_changed = true;

  StopList::iterator stop = this->stops.begin();
  int loc = stop->intersection;

  // Update occupancy and trip information
  this->occupancy += stop->passengers;
  
  if (this->occupancy > this->capacity) {
    fprintf(stderr, "CAPACITY EXCEEDED!\n");
    fprintf(stderr, "id %d、occupancy = %d \n", this->id, this->occupancy);
    exit(EXIT_FAILURE);
  }

  if (stop->passengers>0) {
    // fprintf(stderr, ">> PICKED (%d): %.9f (%d,%d) %d %.9f\n", this->id, this->odometer, stop->trip->pick_loc, stop->trip->drop_loc, this->occupancy, this->speed);
    stop->trip->set_picked(this->id);
    stop->trip->wait_time = (this->last_update-stop->distance/this->speed)-stop->trip->trip->pickup_time;
    stop->trip->dist_actual = this->odometer;
    this->speed = stop->trip->speed;
  }
  else if (stop->passengers<0) {
    // fprintf(stderr, ">> DROPPED(%d): %.9f (%d,%d) %d %.9f\n", this->id, this->odometer, stop->trip->pick_loc, stop->trip->drop_loc, this->occupancy, this->speed);
    stop->trip->set_complete(true);
    stop->trip->dist_actual = this->odometer - stop->trip->dist_actual;
    if (++stop!=this->stops.end())
      this->speed = stop->trip->speed;
    else
      this->speed = DEFAULT_SPEED;
  }

  // remove the stop and invalidate the current path
  this->stops.pop_front();
  this->pathIntersection.clear();
  this->pathDistance.clear();
 
  return loc;
}


// Randomly select a place and making the cab go there
inline void Cab::gen_stop(CityMap *city)
{
  // this->cur_pos = -1; return; // if we want cabs to have teleporting capability
  if (this->cur_pos<0) {
    // if (this->id>11000) // jfk
    //   this->cur_pos = 10844;
    // else if (this->id>10500) // lga
    //   this->cur_pos = 10831;
    // else
      this->cur_pos = random()%city->numIntersections();
  }
  int location = -1;
  int distance = -1;
  for (int i=0; i<5 && distance<=0; ++i) {
    // if (this->id>11000) // jfk
    //   location = 10843;
    // else if (this->id>10500) // lga
    //   location = 10830;
    // else
      location = random()%city->numIntersections();
    distance = city->findShortestDistance(this->cur_pos, location);
  }
  if (distance>0) {
    this->stops.push_front(Stop(location, 0, distance, 0, NULL));
    // Assuming the cabs to go back and forth between stops
    this->dist_driven %= distance;
  }
  else 
    this->cur_pos = -1;
}


// Creating a path from src to dst and its computing accumulated
// distance, stored in a reverse order in pathIntersection and
// pathDistance
inline bool Cab::gen_path(CityMap *city, int src, int dst)
{
  CityMap::PathIterator path;
  city->findShortestPathIterator(src, dst, path);
  if (!path.isValid()) return false;
  int acc = path.totalDistance;
  this->pathDistance.clear();
  this->pathIntersection.clear();
  while (acc>0) {
    this->pathIntersection.push_back(path.current());
    this->pathDistance.push_back(acc);
    acc -= path.currentDistance;
    if (path.hasMore()) ++path;
    else break;
  }
  this->pathDistance.push_back(0);
  this->pathIntersection.push_back(src);
  this->cur_index = this->pathDistance.size()-1;
  return true;
}


inline int Cab::cost_to_share(CityMap *city, const CabTrip *trip, ServingOrder *so)
{
  so->reset(-1, this->stops.size());

  // if the cab is undetermined, using the trip as its own
  if (this->cur_pos<0) {
    so->pick = 0;
    return trip->distance;
  }

  // if the cab is available for hire, pick up this trip
  int prev = this->pathIntersection.at(this->cur_index);
  int dis = this->pathDistance.at(this->cur_index)-this->dist_driven;
  if (this->stops.front().passengers==0) {
    const int d = city->findShortestDistanceReverse(prev, trip->pick_loc);
    if (d<0 || d+dis>MAX_DELAY_DISTANCE)
      return -1;
    so->pick = 0;
    return dis+d+trip->distance;
  }
  
  // otherwise, do full calculation. There is a fixed cost of dropping
  // of this trip after the last dropoff location
  int drop_cost = city->findShortestDistanceReverse(this->stops.back().intersection, trip->drop_loc);

  // ... but if the path doesn't exist, bail out
  if (drop_cost<0) return -1;

  // Next, we need to determine how soon can we start take this trip
  // in given the max number of shares. Since we always put this trip
  // dropoff at the end, the number of shares will increase for all
  // trips that would be dropped off between the start of this trip to
  // the end. So we need to look pass the latest dropoff that already
  // has the maximum number of shares. If there's none, we start at
  // the beginning.
  StopList::iterator skip_it;
  int vacancy = this->find_shareable_stop(skip_it, trip->trip->passengers);
  bool skip = skip_it->trip->shares+1>this->max_share || vacancy<0 || skip_it!=this->stops.begin();
  //if (skip && (skip_it==--this->stops.end())) return -1;

  // Now we try all possible segment, only after the skipped trip
  int occ = this->occupancy;
  int order=0;
  int min_cost = INT_MAX;
  int pick_dist = 0; // the distance from the pick location to the next stop
  for (StopList::iterator it=this->stops.begin(); it!=this->stops.end() && dis<MAX_DELAY_DISTANCE; ++it, ++order) {
    const int dist_left = it->distance-((order==0)?this->pathDistance.at(this->cur_index):0);
    // we are not yet at the stop that can accommodate shares
    if (skip)
      skip = it!=skip_it;
    // check if the passengers would fit in the cab
    else if (it->occ+trip->trip->passengers<=this->capacity) {
      // and the distance from here to when we pick them up should meet our condition
      int d = city->findShortestDistanceReverse(prev, trip->pick_loc);
      if ((d>=0) && (dis+d<=MAX_DELAY_DISTANCE)) {
        int cost = d;
        d = city->findShortestDistance(trip->pick_loc, it->intersection);
        if (d>=0 && (d+it->dist_acc+drop_cost-trip->distance)<=MAX_EXTRA_DISTANCE) {
          cost += d-dist_left;
          if ((cost+it->max_extra)<=MAX_EXTRA_DISTANCE && (cost+it->max_delay)<=MAX_DELAY_DISTANCE) {
            cost += drop_cost;
            if (cost<min_cost) {
              min_cost = cost;
              pick_dist = d;
              so->pick = order;
            }
          }
        }
      }
    }
    
    prev = it->intersection;
    occ += it->passengers;
    dis += dist_left;
  }
  
  { 
    if (order == this->stops.size()) {
      int d = city->findShortestDistanceReverse(prev, trip->pick_loc);
      if ((d>=0) && (dis+d<=MAX_DELAY_DISTANCE)) {
        int cost = trip->distance + d;
	if (cost<min_cost) {
	  min_cost = cost;
	  pick_dist = d;
          so->pick = order;
	  so->drop = so->pick;
        }
      }
    }
  }
   
  // After finding the pickup order, we'll optimize for the dropoff's
  if (so->pick>=0 && so->pick < this->stops.size()) {
    const int pick_cost = min_cost-drop_cost;
    int max_extra=0, max_delay = 0, last_dist=0;
    int next = -1;
    StopList::iterator it = --this->stops.end();
    for (order=this->stops.size()-1; ; --order, --it) {
      
      int intersection = (order<so->pick)?trip->pick_loc:it->intersection;
      if (next>=0) {
        int cost = city->findShortestDistance(trip->drop_loc, next);
        if (cost>=0) {
          int d = city->findShortestDistanceReverse(intersection, trip->drop_loc);
          if (d>=0) {
	   
            cost += pick_cost+d-last_dist;
            if ((cost+max_extra<MAX_EXTRA_DISTANCE) && cost<min_cost && cost+max_delay<MAX_DELAY_DISTANCE) {
              min_cost = cost;
              so->drop = order+1;
            }
          }
        }
      }
      if (order<so->pick) break;
      next = intersection;
      last_dist = (order==so->pick)?pick_dist:it->distance;
      max_extra = it->max_extra;
      max_delay = it->max_delay;
    }
  }
  return min_cost;
}


// We need to determine how soon can we start take this trip in given
// the max number of shares. Since we always put this trip dropoff at
// the end, the number of shares will increase for all trips that
// would be dropped off between the start of this trip to the end. So
// we need to look pass the latest dropoff that already has the
// maximum number of shares. If there's none, we start at the
// beginning.
inline int Cab::find_shareable_stop(StopList::iterator &skip_it, int num_ppl)
{
  //printf(stderr, "in find_shareable_stop\n");
  int vacancy;
  if (!this->shareability_changed && num_ppl == 1) {
    skip_it = this->saved_stop.first;
    vacancy = this->saved_stop.second;
  }
  else {
    int max_extra = 0;
    int max_delay = 0;
    int dist_acc = 0;
    skip_it = --this->stops.end();
    vacancy = this->max_share;
    while (1) {
      if (skip_it->passengers<0) {
        --vacancy;
        if (max_extra<skip_it->trip->dist_extra)
          max_extra = skip_it->trip->dist_extra;
      }
      else if (skip_it->passengers>0) {
	if (max_delay<skip_it->trip->dist_delay)
	  max_delay = skip_it->trip->dist_delay;
      }
      skip_it->max_extra = max_extra;
      skip_it->dist_acc = dist_acc;
      dist_acc += skip_it->distance;
      skip_it->max_delay = max_delay;
      if (skip_it==this->stops.begin() || skip_it->trip->shares>=this->max_share || vacancy<0 || 
	  skip_it->occ+num_ppl > this->capacity)
        break;
      --skip_it;
    }
    

    this->saved_stop.first = skip_it;
    this->saved_stop.second = vacancy;
    this->shareability_changed = false;
  }
  return vacancy;
}

inline void Cab::add_trip(CityMap *city, CabTrip *trip, const ServingOrder &so)
{

  StopList::iterator it = this->stops.begin();
  std::advance(it, so.pick);
  StopList::iterator drop_it = it;
  if (so.drop<this->stops.size())
    std::advance(drop_it, so.drop-so.pick);
  else
    drop_it = this->stops.end();

  int occ_pick=-1, occ_drop=-1;
  StopList::iterator stop = it;
  if (so.pick == 0 && it!= this->stops.end() && it->passengers<0) {
    occ_pick = it->occ + trip->trip->passengers;
  } else if (so.pick == 0 && it!= this->stops.end() && it->passengers>0) {
    occ_pick = it->occ - it->passengers + trip->trip->passengers;
  } else if (so.pick == 0 || it == this->stops.end()) {
    occ_pick = trip->trip->passengers;
  } else {
    if (stop!=this->stops.begin()){
      --stop;
      if (stop->passengers < 0)
	occ_pick = stop->occ + stop->passengers + trip->trip->passengers;
      else occ_pick = stop->occ + trip->trip->passengers;
      ++stop;
    }
  }

  // Increase the number of shares all trips that will be dropped and
  // increase the number of stops for only trips that have been
  // picked. For the trip being served, calculating the number of
  // shares based on pickup and dropoff.
  {
    trip->stops = 0;
    trip->shares = 0;

    for (; stop!=drop_it; ++stop) {
      if (stop->passengers<0) {
        ++trip->shares;
        ++stop->trip->shares;
        if (stop->trip->is_picked())
          ++stop->trip->stops;
      }
      if (stop->passengers)
        ++trip->stops;
      stop->occ += trip->trip->passengers; 
    }

    // increase additional stops for those after this dropoff and
    // increase shares only for trips picked before this dropped off
    for (; stop!=this->stops.end(); ++stop) {
      if (stop->passengers>0)
        --stop->trip->shares;
      else if (stop->passengers<0)
        ++stop->trip->shares;
      if (stop->trip->is_picked())
        ++stop->trip->stops;
    }
  }

  StopList::iterator temp = drop_it;
  if (so.pick == so.drop || it->passengers == 0) {
    occ_drop = occ_pick;
  } else if (stops.size()!=0) {
    --temp;
    if (temp->passengers < 0) {
      occ_drop = temp->occ + temp->passengers;
    } else {
      occ_drop = temp->occ;
    }
  }

  
  int dist_extra = (it==this->stops.end())?0:it->distance;
  // Now inserting the trip. If this is the only trip
  if (it==this->stops.end()) {
    this->stops.push_back(Stop(trip->pick_loc, trip->trip->passengers, 0.f, trip->trip->passengers, trip));
    this->stops.push_back(Stop(trip->drop_loc, -trip->trip->passengers, trip->distance, trip->trip->passengers, trip));
    trip->dist_extra = 0;

  // otherwise, try to put it in between two other stops
  } else {
    // update the distance of the trip if the taxi is not roaming
    const bool roaming = this->stops.front().passengers==0;
    if (!roaming)
      it->distance = city->findShortestDistance(trip->pick_loc, it->intersection);
    dist_extra = it->distance - dist_extra;
    // for the first stop, interpolate between cur_index and the first stop
    if (it==this->stops.begin()) {
      this->dist_driven -= this->pathDistance.at(this->cur_index);
      this->cur_pos = this->pathIntersection.at(this->cur_index);
      const int distance = city->findShortestDistanceReverse(this->cur_pos, trip->pick_loc);
      const Stop stop(trip->pick_loc, trip->trip->passengers, distance, occ_pick, trip);
      if (!roaming) {
        this->stops.push_front(stop);
        dist_extra += distance+this->pathDistance.at(this->cur_index);
      }
      else {
        (*it) = stop;
        ++it;
      }
      this->gen_path(city, this->cur_pos, trip->pick_loc);

    // otherwise, it wouldn't affect our current path, we just need to insert the stop
    } else {
      StopList::iterator it2 = it;
      --it2;
      const int distance = city->findShortestDistanceReverse(it2->intersection, trip->pick_loc);
      this->stops.insert(it, Stop(trip->pick_loc, trip->trip->passengers, distance, occ_pick, trip));
      dist_extra += distance;
    }


    
    // add the (pickup) extra distance to the rest of the stops until the dropoff location  
    for (; it!=drop_it; ++it) {
      trip->dist_extra += it->distance;
      if (it->passengers<0) {
        it->trip->dist_extra += dist_extra;
      } else if (it->passengers>0) {
	it->trip->dist_extra -= dist_extra;
	it->trip->dist_delay += dist_extra;
      }
    }
    --it;
  
    const int distance = city->findShortestDistanceReverse(it->intersection, trip->drop_loc);
    this->stops.insert(drop_it, Stop(trip->drop_loc, -trip->trip->passengers, distance, occ_drop, trip));
    trip->dist_extra += distance-trip->distance;
    
    // add the (dropoff) extra distance to the rest of the stops until the dropoff location
    if (drop_it!=this->stops.end()) {
      const int drop_cost = city->findShortestDistance(trip->drop_loc, drop_it->intersection);
      dist_extra += distance + drop_cost - drop_it->distance;
      drop_it->distance = drop_cost;
      for (it=drop_it; it!=this->stops.end(); ++it) {
        if (it->passengers<0) {
          it->trip->dist_extra += dist_extra;
        } else if (it->passengers>0) {
          it->trip->dist_extra -= dist_extra;
	  it->trip->dist_delay += dist_extra;
	}
      }
    }
  }

  this->shareability_changed = true;

}

#endif
