#ifndef CAB_TRIP_HPP
#define CAB_TRIP_HPP

#include <stdio.h>
#include <iostream>
#include "CityMap.hpp"
#include "KdTrip.hpp"

class CabTrip
{
public:
  const KdTrip::Trip * trip;
  
  int pick_loc;
  int drop_loc;
  int stops;
  int shares;
  int picked_id;
  int dist_actual;
  int dist_extra;
  int distance;
  int speed;
  int dist_delay;
  int wait_time;
private:
  bool     complete;

public:
  CabTrip() { this->init(-1, -1, 0); }
  CabTrip(int src, int dst, const KdTrip::Trip* trip) { this->init(src, dst, trip); }
  void init(int src, int dst, const KdTrip::Trip *trip);
  bool is_complete() const;
  void set_complete(bool); // 0 for not served, 1 for being served, 2 for completed trip 
  bool is_picked() const;
  void set_picked(int);
  void computeSpeed();

  float actual_dist() const { return this->dist_actual*1e-6f; }
  float extra_dist() const { return this->dist_extra*1e-6f; }
};

typedef std::vector<CabTrip> CabTripList;

inline bool compareTrips(const CabTrip* t1, const CabTrip* t2)
{
  return (*(t1->trip)) < (*(t2->trip)) ;

}

inline void CabTrip::init(int src, int dst, const KdTrip::Trip* trip)
{
  this->trip = trip;
  this->pick_loc = src;
  this->drop_loc = dst;
  this->picked_id = INT_MIN;
  this->dist_actual = 0;
  this->dist_extra = 0;
  this->complete = false;
  this->stops = 0;
  this->shares = 0;
  this->distance = -1;
  this->computeSpeed();
  this->dist_delay = 0;
  this->wait_time = 0;
}

inline bool CabTrip::is_complete() const
{
  return this->complete;

}

inline void CabTrip::set_complete(bool complete)
{
  this->complete = complete;
}

inline bool CabTrip::is_picked() const
{
  return this->picked_id!=INT_MIN;
}

inline void CabTrip::set_picked(int id)
{
  this->picked_id = id;
}

inline void CabTrip::computeSpeed()
{
  this->speed = 0;
  if (trip) {
    const int diff = this->trip->dropoff_time-this->trip->pickup_time;
    if (diff>0)
      this->speed = this->trip->distance*1e4f/diff + 0.5;
  }
}

inline void gen_cabtrips(CityMap *city, const KdTrip::Trip *trips, int nTrip, int total_trips, CabTripList &cabtrips, time_t start_time, int duration, float min_speed=3.f)
{
  int src, dst;
  bool found;
  int ms = min_speed*1e6f/3600;
  cabtrips.resize((unsigned long) std::min(total_trips, nTrip));
  std::cout<<cabtrips.size()<<std::endl;
  const KdTrip::Trip * it = trips;
  CabTrip *ct = &cabtrips[0];
  // int skipTrip = 1;
  int skipTrip = nTrip/total_trips;
  for (; nTrip>0 && total_trips>0; nTrip-=skipTrip, it+=skipTrip) {
    src = city->mapToIntersection(CityMap::Location(it->pickup_lat, 
                                                    it->pickup_long));
    dst = city->mapToIntersection(CityMap::Location(it->dropoff_lat, 
                                                    it->dropoff_long));
      //std::cout<<"src"<<"="<<src<<std::endl;
      //std::cout<<"dst"<<"="<<dst<<std::endl;
    if ((src!=-1) && (dst!=-1) && (src!=dst) && (it->distance !=0) 
        && (it->passengers < 5) && (it->passengers > 0)
        && (city->pathExists(src, dst)) 
	    && ((start_time == -1)|| (it->pickup_time >= start_time && it->pickup_time < start_time + duration)))
        { // && ((src>=10819)||(dst>=10819)))
        ct->init(src, dst, it);
        if (ct->speed<ms) continue;
        ct->distance = city->findShortestDistance(ct->pick_loc, ct->drop_loc);
        --total_trips;
        ct++;
        }
  }
  cabtrips.resize(ct-&cabtrips[0]);
}

#endif
