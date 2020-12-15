#include <omp.h>
#include <unistd.h>
#include <stdlib.h>
#include <pthread.h>

void do_stuff(int);

int main() {
    omp_lock_t lock;
    int iter = 0;

#pragma omp parallel
    // forgot to lock this check!
    while (iter < 583583) {
        omp_set_lock(&lock);
        int task = iter++;
        omp_unset_lock(&lock);

        do_stuff(task);
    }

}

