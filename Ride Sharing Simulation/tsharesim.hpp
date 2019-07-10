#ifndef TSHARESIM_HPP
#define TSHARESIM_HPP
#include "CityMap.hpp"
#include "Cab.hpp"

#define TSHARESIM_BEGIN namespace tsharesim {
#define TSHARESIM_END }

TSHARESIM_BEGIN
void init(CityMap *city, const char *edgeFile, ::Cab **cabs, int total_cabs, int num_share);

class Cab : public ::Cab {
public:
  Cab(int num_share, int cap=4, int id=-1);
  virtual int   update_cab(CityMap *city, int time);
  virtual int   cost_to_share(CityMap *city, const CabTrip *trip, ServingOrder *so);
  virtual void  add_trip(CityMap *city, CabTrip *trip, const ServingOrder &order);

  int lastValue;
};
TSHARESIM_END

#endif
