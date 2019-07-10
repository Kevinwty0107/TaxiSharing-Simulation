#include <stdio.h>
#include <time.h>
#include "KdTrip.hpp"
#include <boost/date_time/gregorian/gregorian_types.hpp>

int main(int argc, char **argv)
{
  if (argc<4) {
    fprintf(stderr, 
            "Usage: %s  <IN_TAXI_TRIP_RECORDS_FILE> <OUTPUT_DIR>\n", 
            argv[0]);
    return -1;
  }

  boost::gregorian::date date(2008, 12, 31);
  boost::gregorian::days oneDay(1);
  uint64_t secsPerDay = 24*60*60;
  uint64_t time  = KdTrip::Query::createTime((int)date.year(), (int)date.month(), (int)date.day(), 4, 0, 0) + secsPerDay;
  boost::iostreams::mapped_file mfile(std::string(argv[1]),
                                      boost::iostreams::mapped_file::priv);
  int nTrip = mfile.size()/sizeof(KdTrip::Trip);
  KdTrip::Trip *trips = (KdTrip::Trip*)mfile.const_data();

  char fn[128];
  FILE *fo = 0;
  int count;
  for (int i=0; i<nTrip; ++i, ++trips) {
    while (trips->pickup_time>=time) {
      if (fo) {
        fprintf(stderr, "%d\n", count);
        fclose(fo);
        fo = 0;
      }
      time += secsPerDay;
      date += oneDay;
    }
    if (!fo) {
      sprintf(fn, "%s/%4d_%02d_%02d.bin", argv[2], (int)date.year(), (int)date.month(), (int)date.day());
      fprintf(stderr, "%s: ", fn);
      fo = fopen(fn, "wb");
      count = 0;
    }
    fwrite(trips, sizeof(KdTrip::Trip), 1, fo);
    count++;
  }
  if (fo) {
    fprintf(stderr, "%d\n", count);
    fclose(fo);
  }

  return 0;
}
