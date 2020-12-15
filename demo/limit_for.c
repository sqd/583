#include <omp.h>
#include <unistd.h>
#include <stdlib.h>
#include <pthread.h>

int main() {
    int arr[583];
#pragma omp parallel for
    for (int i = 0; i < 583; i++)
        arr[i] = i;

}

