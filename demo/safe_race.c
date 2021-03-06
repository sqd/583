#include <omp.h>
#include <unistd.h>
#include <stdlib.h>
#include <pthread.h>

int main() {
    omp_lock_t lock;
    int sum = 0;
#pragma omp parallel
    while (1) {
        int tid = omp_get_thread_num();
        omp_set_lock(&lock);
        if (tid % 2)
            sum += 583;
        else
            sum -= 583;
        omp_unset_lock(&lock);
    }

}

