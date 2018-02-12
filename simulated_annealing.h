#include <math.h>

#define FALSE 0
#define TRUE !FALSE

#define MAX_STRING_LENGTH 3
#define TARGET_UTILISATION 7.8
#define MIN_PROCESSORS ((const int) ceil (TARGET_UTILISATION))
#define MAX_PROCESSORS MIN_PROCESSORS+2
#define NUM_TASKS 50*MAX_PROCESSORS
#define HARMONIC_PERIODS TRUE
#define MIN_PERIOD 250000
#define MAX_PERIOD 10000000
#define PERIOD_STEP 1000

#define RELEASE_OVERHEAD 1
#define PREEMPTION_COST 1
#define PREEMPTIVE TRUE
#define HEADSTART_BY_DMPO TRUE

#define DEBUG FALSE

#define INITIAL_TEMPERATURE 1000
#define INITIAL_MAX_MOVES 1000
#define MAX_MOVES_SINCE_BEST 50
#define INCREASE_PASSES_ON_SUCCESS TRUE
#define INCREASE_ON_SUCCESS 2
#define MOVES_BETWEEN_COOLING 50
#define COOLING_FACTOR 0.99
#define RESEED_FACTOR 250
#define TYPES_OF_MODIFY 2

typedef struct
{
    char name[MAX_STRING_LENGTH];
    int period;
    int deadline;
    int jitter; // note requirement, not release jitter
    int priority;
    int offset;
    int wcet;
    int wcrt;
    int affinity;
} task;
