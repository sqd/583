#include <omp.h>
#include <unistd.h>
#include <stdlib.h>

void do_other_thing() {

}

int main() {
    omp_lock_t lock;
    int* const i = malloc(4);
#pragma omp parallel
    while(1)
    {
        omp_set_lock(&lock);
        if(*i == 999) {
            *i += 233;
            omp_unset_lock(&lock);
        } else {
            *i += 666;
            omp_unset_lock(&lock);
        }
    }
#pragma omp parallel
    do_other_thing();
}
