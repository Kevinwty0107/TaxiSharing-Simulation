#ifndef SIMULATOR_HPP
#define SIMULATOR_HPP

#include <boost/thread/thread.hpp>
#include <boost/atomic.hpp>
#include <time.h>
#include "Cab.hpp"
#include "stdlib.h"
#include <stdlib.h>
#include <string.h>


class Simulator
{
public:
    static const int CABS_PER_CHUNK = 100;

    struct Parameters {
        CityMap * city;
        Cab    ** cabs;
        int       total_cabs;
        int       num_share;
        CabTrip * trip;
        int       num_trips;
    };

    struct Solution {
        Solution() { this->reset(); }
        void reset() {
            this->min_cost = INT_MAX;
            this->min_cab_num = -1;
            this->min_serving_order.reset();
        }

        bool operator<(const Solution &s) const {
            return (this->min_cost<s.min_cost) || (this->min_cost==s.min_cost && this->min_cab_num<s.min_cab_num);
        }

        int               min_cost;
        int               min_cab_num;
        Cab::ServingOrder min_serving_order;
    };

    Simulator(int n=0): shutdown(true) {
        this->start(n);
    }

    void start(int n) {
        if (!this->shutdown)
            return;
        this->shutdown = false;
        this->nThreads = n;
        this->workerBusy = this->nThreads;
        this->params.num_trips = 0;
        if (n<2)
            return;
        for (int i=0; i<this->nThreads; i++) {
            this->workerThreads.create_thread(boost::bind(&Simulator::worker, this, i));
        }
        this->waitForWorkers();
    }

    void stop() {
        this->shutdown = true;
        this->condWork.notify_all();
    }

    void init(CityMap *city, Cab **cabs, int total_cabs, int num_share) {
        this->params.city = city;
        this->params.cabs = cabs;
        this->params.total_cabs = total_cabs;
        this->params.num_share = num_share;
        this->numServed = 0;
        this->totalCost = 0;
        this->hourlyCost.resize(24, 0);
    }

    void dispatchToWorkers(CabTrip *trips, int cnt)
    {
        this->solution.reset();
        this->currentCab.store(0, boost::memory_order_release);
        this->workerBusy = this->nThreads;
        this->condWork.notify_all();
    }

    void waitForWorkers() {
        boost::mutex::scoped_lock lock(this->mutex);
        if (this->workerBusy>0)
            this->condDone.wait(lock);
    }

    void worker(int workerId) {
        Solution local;
        while (1) {
            {
                boost::mutex::scoped_lock lock(this->mutex);
                if (local<this->solution)
                    this->solution = local;
                if (--this->workerBusy==0) {
                    this->applySolution();
                    this->workerBusy = this->nThreads;
                    if (--this->params.num_trips>0) {
                        ++this->params.trip;
                        this->currentCab.store(0, boost::memory_order_release);
                        this->solution.reset();
                        this->condWork.notify_all();
                    } else {
                        this->condDone.notify_all();
                        this->condWork.wait(lock);
                    }
                }
                else {
                    this->condWork.wait(lock);
                }
            }
            if (this->shutdown) break;

            local.reset();
            int index;
            while ((index=this->currentCab.fetch_add(CABS_PER_CHUNK, boost::memory_order_relaxed))<this->params.total_cabs) {
                this->updateCost(this->params.trip, index, std::min(index+CABS_PER_CHUNK, this->params.total_cabs), &local);
            }
        }
    }



    void applySolution() {
        if (this->solution.min_cab_num!=-1) {
            this->params.cabs[this->solution.min_cab_num]->add_trip(this->params.city,
                                                                    this->params.trip,
                                                                    this->solution.min_serving_order);
            this->totalCost += this->solution.min_cost;
            time_t c_time = (time_t)this->params.trip->trip->pickup_time;
            struct tm *cur_time = localtime(&c_time);
            this->hourlyCost[cur_time->tm_hour] += this->solution.min_cost;
            ++this->numServed;
        }
    }

#define MAXN 1000000                  //MAXN represents the maximum number of vertices of the X set and the Y set
    int nx,ny;                        //Number of vertices in the X and Y sets
    int g[MAXN][MAXN];                //Adjacency matrix, g[i][j] is 1 for connection
    int cx[20000],cy[10000];        //cx[i], which represents the index of the vertex in the set Y that matches the element Xi in the x set in the final maximum match.
//cy[i], which represents the index of the vertex in the set X that matches the element Yi in the y set in the final maximum match.

//The data mk[i]=0 in the DFS algorithm for recording the vertex access status indicates that it has not been accessed, and 1 indicates that the data has been accessed.
    int mk[MAXN];
    int trip2cab[MAXN];


//Starting from the fixed vertex u in the set X, use the strategy with limited depth to find the augmented path
//This augmentation path can only increase the current number of matches by 1.
    int path(int u){
        for(int v=0;v<ny;++v){      //Consider all Yi vertex v
            if(g[u][v] && !mk[v]){     //The vertex v in Y is adjacent to u and has not been visited.
                mk[v]=1;

                //If v hasn't been matched, then match v directly to u. If v has been matched,
                // but start from cy[v], which is the x that has been matched before v,
                // find an augmented path, but remember here that v has been visited
                //If the first condition is true, it will not be called recursively
                if(cy[v]==-1 || path(cy[v])){
                    cx[u]=v;         //Match Y in v to X in u
                    cy[v]=u;            //Match the u in the X to the Y in the v
                    return 1;
                }
            }
        }
        return 0;                        //If there is no augmentation path starting from u, return 0
    }

    int maxMatch(){        //Hungarian algorithm for finding the maximum matching of bipartite graphs
        int res=0;
        memset(cx,-1,sizeof(cx));
        //Start widening from 0 match, initialize each element of cx and cy to -1
        memset(cy,-1,sizeof(cy));

        for(int i=0;i<nx;++i){
            if(cx[i]==-1){               //Start looking for an augmentation path from each point in the X set that has not been matched.
                memset(mk,0,sizeof(mk));
                res+=path(i);
            }
        }
        return res;
    }

    int *hungarian(CabTrip *inicab_trips, int start, int end, Solution *local, int numtrip ){

        //memset(g, 0, sizeof(g[0][0]) * MAXN * MAXN);
        for(int j = 0; j < 1000; j++)
        {
            for(int i = 0; i < 10000; i++)
            {
                g[j][i] = 0;
            }
        }
        this->params.trip = inicab_trips;
        this->params.num_trips = numtrip;
        int add_cost;
        Cab::ServingOrder serving_order;
        if (this->nThreads<2) {
            for (int j=0; j<numtrip; ++j, ++this->params.trip) {
                for (int i=start; i<end; ++i) {
                    add_cost = this->params.cabs[i]->cost_to_share(this->params.city, this->params.trip, &serving_order);
                    if (serving_order.isValid() && (add_cost<local->min_cost)) {
                        g[i][j]=1;

                    }
                }

            }
            nx=end-start;
            ny=numtrip;
            memset(cx,-1,sizeof(cx));
            memset(cy,-1,sizeof(cy));
            for(int i=0;i<10000;i++){cy[i]=-1;}
            for(int i=0;i<20000;i++){cx[i]=-1;}
            cout<<cy[1]<<endl;
            maxMatch();
            memset(trip2cab,-1,sizeof(trip2cab));
            for (int j=0; j<numtrip; ++j, ++this->params.trip) {
                trip2cab[j] = cy[j];
            }
        }
        return trip2cab;
    }


    void updateCost(CabTrip *cab_trip, int start, int end, Solution *local) {
        int add_cost;
        Cab::ServingOrder serving_order;
        for (int i=start; i<end; ++i) {
            this->params.cabs[i]->update_cab(this->params.city, cab_trip->trip->pickup_time);

            add_cost = this->params.cabs[i]->cost_to_share(this->params.city, cab_trip, &serving_order);
            if (serving_order.isValid() && (add_cost<local->min_cost)) {
                local->min_cost = add_cost;
                local->min_cab_num = i;
                local->min_serving_order = serving_order;
            }
        }
    }

    void updateCosti(CabTrip *cab_trip, int i, Solution *local) {
        int add_cost;
        Cab::ServingOrder serving_order;
        this->params.cabs[i]->update_cab(this->params.city, cab_trip->trip->pickup_time);
        add_cost = this->params.cabs[i]->cost_to_share(this->params.city, cab_trip, &serving_order);
        if (serving_order.isValid() && (add_cost<local->min_cost)) {
            local->min_cost = add_cost;
            local->min_cab_num = i;
            local->min_serving_order = serving_order;
        }
    }


    void run(CabTrip *cab_trips, int cnt)
    {
        this->params.trip = cab_trips;
        this->params.num_trips = cnt;
        int *matchcab;
        int size[1000];
        memset(size, 0, sizeof(size));

        CabTrip ***grouptrip = (CabTrip***)malloc(1000 * sizeof(CabTrip**));
        for(int i=0; i<1000; i++)
        {
            grouptrip[i] = (CabTrip**)malloc(10000*sizeof(CabTrip*));
            for(int j=0; j<10000; j++)
            {
                grouptrip[i][j] = (CabTrip*)malloc(sizeof(CabTrip));
            }
        }

        int timestand = cab_trips ->trip->pickup_time;
        for (int i=0; i<cnt; ++i, ++this->params.trip)
        {
            if(this->params.trip->trip->pickup_time < timestand)
                timestand = this->params.trip->trip->pickup_time;
        }


        this->params.trip = cab_trips;

        int s=0;
        //int j=0;
        for (int t=0; t<cnt; ++t, ++this->params.trip) {
            //if((this->params.trip->trip->pickup_time)-timestand <= (i+1)*900) {cout<<this->params.trip->trip->pickup_time<<" ";}
            //if((this->params.trip->trip->pickup_time)-timestand <= (i+1)*900 && (this->params.trip->trip->pickup_time)-timestand >= i*900)
            int i= ((this->params.trip->trip->pickup_time)-timestand) /1500;
            s=max(i,s);
            grouptrip[i][size[i]] = this->params.trip;
            size[i]++;
        }

        cout<<"s="<<s<<endl;
        this->params.trip = cab_trips;
        if (this->nThreads<2) {

            for(int j=0; j<s; ++j) {
                matchcab = hungarian(grouptrip[j][0], 0, this->params.total_cabs, &this->solution, size[j]);
                int a = *(matchcab+1);
                cout<<a;
                for (int i = 0; i < size[j]; ++i) {
                    this->solution.reset();
                    if (*(matchcab + i) != -1) {
                        this->updateCosti(grouptrip[j][i], *(matchcab + i), &this->solution);
                        this->applySolution();
                    }
                }
            }
            return;
        }
        this->dispatchToWorkers(cab_trips, cnt);
        this->waitForWorkers();
    }

    int count() const {
        return this->numServed;
    }

    float total_cost() const {
        return this->totalCost*1e-6f;
    }

    std::vector<float> hourly_cost() {
        std::vector<float> hourly(24, 0.0);
        for (int i=0; i<24; i++) {
            hourly[i] = this->hourlyCost[i]*1e-6f;
        }
        return hourly;
    }

private:

    Simulator::Parameters       params;
    boost::mutex                mutex;
    boost::condition_variable   condDone, condWork;
    boost::thread_group         workerThreads;
    Solution                    solution;
    bool                        shutdown;
    int                         nThreads;
    int                         workerBusy;
    boost::atomic<int>          currentCab;

    int                         numServed;
    int64_t                     totalCost;
    std::vector<int64_t>        hourlyCost;
};

#endif
