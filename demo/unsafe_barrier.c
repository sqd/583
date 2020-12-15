#include <omp.h>
#include <unistd.h>
#include <stdlib.h>
#include <pthread.h>

int main() {
    int sum = 0;
#pragma omp parallel
    {
        int *alias = &sum;
        if(omp_get_thread_num() % 2) {
            *(alias+1-1) += 583;
        } else
            *(alias-2+1+1) += 583;
    }

}

