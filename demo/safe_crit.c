#include <omp.h>
#include <unistd.h>
#include <stdlib.h>
#include <pthread.h>

int main() {
    int sum = 0;
#pragma omp parallel
    while (1) {
        int tid = omp_get_thread_num();
        if (tid % 2)
#pragma omp critical(same_critical_section)
            sum += 583;
        else
#pragma omp critical(same_critical_section)
            sum -= 583;
    }

}

