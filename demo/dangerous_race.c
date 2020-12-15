#include <omp.h>
#include <unistd.h>
#include <stdlib.h>
#include <pthread.h>

int main() {
    int sum = 777;
#pragma omp parallel
    while (1) {
        int tid = omp_get_thread_num();
        if (tid % 2)
            sum += 333;
        else
            sum -= 444;
    }

}

