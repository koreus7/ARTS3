#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <limits.h>
#include <time.h>
#include <assert.h>

#include "simulated_annealing.h"

void load_task_set (task *tasks)
{
    tasks[0] = (task) {.name = "A", .period = 1000, .deadline = 20, .jitter = 0, .priority = 0, .offset = 0, .wcet = 3, .wcrt = 0};
    tasks[1] = (task) {.name = "B", .period = 100, .deadline = 100, .jitter = 0, .priority = 0, .offset = 0, .wcet = 10, .wcrt = 0};
    tasks[2] = (task) {.name = "C", .period = 50, .deadline = 50, .jitter = 0, .priority = 0, .offset = 0, .wcet = 20, .wcrt = 0};
    tasks[3] = (task) {.name = "D", .period = 57, .deadline = 10, .jitter = 0, .priority = 0, .offset = 0, .wcet = 5, .wcrt = 0};
    tasks[4] = (task) {.name = "E", .period = 33, .deadline = 33, .jitter = 0, .priority = 0, .offset = 0, .wcet = 1, .wcrt = 0};
    tasks[5] = (task) {.name = "F", .period = 7, .deadline = 7, .jitter = 0, .priority = 0, .offset = 0, .wcet = 1, .wcrt = 0};
}

double randFraction()
{
    return ((double)rand()) / ((double) RAND_MAX);
}

static int log_rnd(
                   int min,
                   int max,
                   int step
                   )
{
    double log_interval, log_period;
    
    // generate task period maxT is max period, minT is minimum period
    log_interval = log((double) (max)) - log((double) min);
    log_period = log((double) min) + (randFraction() * log_interval);
    
    return ((int) log_period) * step;
}

static int rnd(
               int min,
               int max,
               int step
               )
{
    uint64_t x;
    
    assert((uint32_t)INT_MAX < UINT32_MAX);
    assert((uint32_t)RAND_MAX < UINT32_MAX);
    assert(min >= 0 && min <= max);
    assert(step >= 1 && (step - 1) <= (max - min));
    
    x = (uint64_t)rand();
    x = x * ((uint64_t)(max - min) + 1);
    x = x / (((uint64_t)step * (uint64_t)(RAND_MAX)) + 1);
    x = x * step;
    x = x + min;
    assert((uint64_t)min <= x && x <= (uint64_t)max);
    assert(((x - (uint64_t)min) % (uint64_t)step) == 0);
    
    return ((int) x);
}

int order_deadline (const void *lhs, const void *rhs)
{
    if (((task*)lhs)->deadline == ((task*)rhs)->deadline)
        return strcmp(((task*)lhs)->name, ((task*)rhs)->name);
    
    return (((task*)lhs)->deadline - ((task*)rhs)->deadline);
}

int order_period (const void *lhs, const void *rhs)
{
    if (((task*)lhs)->period == ((task*)rhs)->period)
        return strcmp(((task*)lhs)->name, ((task*)rhs)->name);
    
    return (((task*)lhs)->period - ((task*)rhs)->period);
}

void perform_dmpo (task *tasks, const int num_tasks)
// procedure that performs dmpo
{
    int i, j;
    int min_deadline, min_index;
    int next_priority = 1;
    
    for (i = 0; i < num_tasks; i++)
        tasks[i].priority = 0;
    
    qsort(tasks, NUM_TASKS, sizeof(task), order_deadline);
    
    for (i = 0; i < NUM_TASKS; i++)
        tasks[i].priority = i;
}

int schedulability_analysis (task *tasks, const int num_tasks, int OVERHEADS)
{
    int i, j;
    int prev_wcrt = 0;
    int hp_releases = 0;
    int worst_case_interference = 0;
    int blocking = 0;
    int unschedulable = 0;
    
    if (!PREEMPTIVE)
    {
        for (i = 0; i < num_tasks; i++)
            if (tasks[i].wcet > blocking)
                blocking = tasks[i].wcet;
    }
    
    /*  do the standard schedulability analysis */
    for (i = 0; i < num_tasks; i++)
    {
        /* initialise the wcrt */
        prev_wcrt = 0;
        tasks[i].wcrt = tasks[i].wcet;
        
        /* recursively calculate the wcrt */
        while ((prev_wcrt < tasks[i].wcrt) && (tasks[i].wcrt <= tasks[i].period))
        {
            prev_wcrt = tasks[i].wcrt;
            tasks[i].wcrt = tasks[i].wcet;
            if (OVERHEADS)
                tasks[i].wcrt += (NUM_TASKS*RELEASE_OVERHEAD);
            
            /* calculate the worst_case_interference */
            for (j = 0; j < i; j++)
            {
                hp_releases = (prev_wcrt + tasks[j].jitter) / tasks[j].period;
                if ((prev_wcrt + tasks[j].jitter) % tasks[j].period != 0)
                    hp_releases++;
                if (OVERHEADS)
                    worst_case_interference = hp_releases * (tasks[j].wcet+PREEMPTION_COST+RELEASE_OVERHEAD);
                else
                    worst_case_interference = hp_releases * tasks[j].wcet;
                tasks[i].wcrt += worst_case_interference;
            }
        }
        
        /* adapt the wcrt for release jitter, offsets and blocking */
        tasks[i].wcrt += tasks[i].jitter;
        tasks[i].wcrt += tasks[i].offset;
        tasks[i].wcrt += blocking;
    }
    
    for (i = 0; i < num_tasks; i++)
        if (tasks[i].wcrt > tasks[i].deadline)
            unschedulable++;
    
    return unschedulable;
}

void print_task_set (task *tasks, const int num_tasks)
{
    int i;
    
    printf ("Id\t T\t D\t J\t P\t O\t C\t R\t Sched\n");
    for (i = 0; i < num_tasks; i++)
    {
        printf ("%s\t %d\t %d\t %d", tasks[i].name, tasks[i].period, tasks[i].deadline, tasks[i].jitter);
        printf ("\t %d\t %d\t %d\t %d", tasks[i].priority, tasks[i].offset, tasks[i].wcet, tasks[i].wcrt);
        if (tasks[i].wcrt <= tasks[i].deadline)
            printf ("\t Y\n");
        else
            printf ("\t N\n");
    }
}

void sensitivity_analysis_individual_tasks (task *tasks, const int num_tasks, int OVERHEADS)
{
    int i, j, exit = FALSE, unschedulable;
    int min_wcet = INT_MAX, wcet_sensitivity = 0;
    float initial_multiplier = 16.0;
    float multiplier = initial_multiplier;
    float last_unschedulable_multiplier = multiplier;
    float last_schedulable_multiplier = 1.0;
    task tasks_copy[NUM_TASKS];
    int last_wcet;
    
    for (j=0; j<num_tasks; j++)
    {
        initial_multiplier = 16.0;
        multiplier = initial_multiplier;
        last_unschedulable_multiplier = multiplier;
        last_schedulable_multiplier = 1.0;
        exit = FALSE;
        
        for (i=0; i<num_tasks; i++) {
            tasks_copy[i] = tasks[i];
            if (min_wcet < tasks[i].wcet)
                min_wcet = tasks[i].wcet;
        }
        last_wcet = tasks[j].wcet;
        
        // perform a binary search to find the multiplier
        while (!exit)
        {
            exit = FALSE;
            for (i=0; i<num_tasks; i++)
                tasks_copy[i] = tasks[i];
            tasks_copy[j].wcet = (int) (multiplier * tasks[j].wcet);
            // exit if further changes to the multiplier result in at least one task's WCET not changing
            if (tasks_copy[j].wcet == last_wcet)
                exit = TRUE;
            last_wcet = tasks_copy[j].wcet;
            
            if (!exit)
            {
                unschedulable = schedulability_analysis (tasks_copy, num_tasks, OVERHEADS);
                if (unschedulable == 0)
                {
                    // increase multiplier
                    if (multiplier != initial_multiplier)
                    {
                        last_schedulable_multiplier = multiplier;
                        multiplier += ((last_unschedulable_multiplier - last_schedulable_multiplier)/2);
                    }
                    else
                    {
                        initial_multiplier *= 2;
                        last_unschedulable_multiplier = initial_multiplier;
                        multiplier = last_unschedulable_multiplier;
                    }
                }
                else
                {
                    // reduce multiplier
                    last_unschedulable_multiplier = multiplier;
                    multiplier -= ((last_unschedulable_multiplier - last_schedulable_multiplier)/2);
                }
            }
        }
        
        multiplier = last_schedulable_multiplier;
        // Check that the multiplier results in a schedulable task set
        for (i=0; i<NUM_TASKS; i++)
            tasks_copy[i] = tasks[i];
        tasks_copy[j].wcet = (int) (multiplier * tasks[j].wcet);
        unschedulable = schedulability_analysis (tasks_copy, num_tasks, OVERHEADS);
        if (unschedulable != 0)
            printf ("Sensitivity Analysis Error with multiplier %f\n", multiplier);
        printf ("Task set is schedulable until task %s has its WCET increased by more than %d time units, i.e. multiplier of %f\n",
                tasks[j].name, (tasks_copy[j].wcet - tasks[j].wcet - 1), multiplier);
    }
}

void sensitivity_analysis_all_tasks (task *tasks, const int num_tasks, int OVERHEADS)
{
    int i, j, schedulable, exit = FALSE;
    int min_wcet = INT_MAX, wcet_sensitivity = 0;
    task tasks_copy[NUM_TASKS];
    
    for (j=0; j<NUM_TASKS; j++) {
        tasks_copy[j] = tasks[j];
        if (min_wcet < tasks[j].wcet)
            min_wcet = tasks[j].wcet;
    }
    
    schedulable = schedulability_analysis (tasks_copy, num_tasks, OVERHEADS);
    if (schedulable > 0)
    {
        // task set is un-schedulable so decrease the task's wcet until it is schedulable
        while ((schedulable >= 1) && (wcet_sensitivity < min_wcet) && !exit)
        {
            wcet_sensitivity += 1;
            for (i = 0; i < NUM_TASKS; ++i)
                if (tasks_copy[i].wcet > 1)
                    tasks_copy[i].wcet--;
                else
                    // don't reduce a task's WCET below 0
                    exit = TRUE;
            schedulable = schedulability_analysis (tasks_copy, num_tasks, OVERHEADS);
        }
        if (schedulable == 0)
            printf ("Task set is schedulable when all tasks have their WCET reduced by %d time units\n",
                    (wcet_sensitivity));
        else
            printf ("Task set is not schedulable independent of the reduction in tasks' WCET\n");
    }
    else
    {
        // task set is schedulable so increase the task's wcet until it isn't schedulable
        while (schedulable == 0)
        {
            wcet_sensitivity += 1;
            for (i = 0; i < NUM_TASKS; ++i)
                tasks_copy[i].wcet++;
            schedulable = schedulability_analysis (tasks_copy, num_tasks, OVERHEADS);
        }
        if (wcet_sensitivity >1)
            printf ("Task set is schedulable until all tasks have their WCET increased by more than %d time units\n",
                    wcet_sensitivity - 1);
        else
            printf ("Task set's WCET cannot be increased by any time units\n");
    }
}

void sensitivity_analysis_all_tasks_multiplier (task *tasks, const int num_tasks, int OVERHEADS)
{
    int i, j, exit = FALSE, unschedulable;
    int min_wcet = INT_MAX, wcet_sensitivity = 0;
    float initial_multiplier = 16;
    float multiplier = initial_multiplier;
    float last_unschedulable_multiplier = multiplier;
    float last_schedulable_multiplier = 1.0;
    task tasks_copy[NUM_TASKS];
    int last_wcet[NUM_TASKS];
    
    for (i=0; i<NUM_TASKS; i++) {
        tasks_copy[i] = tasks[i];
        if (min_wcet < tasks[i].wcet)
            min_wcet = tasks[i].wcet;
        last_wcet[i] = tasks[i].wcet;
    }
    
    // perform a binary search to find the multiplier
    while (!exit)
    {
        exit = FALSE;
        for (i=0; i<NUM_TASKS; i++)
        {
            tasks_copy[i] = tasks[i];
            tasks_copy[i].wcet = (int) (multiplier * tasks[i].wcet);
            // exit if further changes to the multiplier result in at least one task's WCET not changing
            if (tasks_copy[i].wcet == last_wcet[i])
                exit = TRUE;
            last_wcet[i] = tasks_copy[i].wcet;
        }
        
        if (!exit)
        {
            unschedulable = schedulability_analysis (tasks_copy, num_tasks, OVERHEADS);
            if (unschedulable == 0)
            {
                // increase multiplier
                if (multiplier != initial_multiplier)
                {
                    last_schedulable_multiplier = multiplier;
                    multiplier += ((last_unschedulable_multiplier - last_schedulable_multiplier)/2);
                }
                else
                {
                    initial_multiplier *= 2;
                    last_unschedulable_multiplier = initial_multiplier;
                    multiplier = last_unschedulable_multiplier;
                }
            }
            else
            {
                // reduce multiplier
                last_unschedulable_multiplier = multiplier;
                multiplier -= ((last_unschedulable_multiplier - last_schedulable_multiplier)/2);
            }
        }
    }
    
    multiplier = last_schedulable_multiplier;
    // Check that the multiplier results in a schedulable task set
    for (i=0; i<NUM_TASKS; i++)
    {
        tasks_copy[i] = tasks[i];
        tasks_copy[i].wcet = (int) (multiplier * tasks[i].wcet);
    }
    unschedulable = schedulability_analysis (tasks_copy, num_tasks, OVERHEADS);
    if (unschedulable != 0)
        printf ("Sensitivity Analysis Error with multiplier %f\n", multiplier);
    else
        printf ("Task set is schedulable until a multiplier of %f is applied to all tasks\n", last_schedulable_multiplier);
}

void generate_task_set (task *tasks)
{
    // generate a schedulable task set for a given target utilisation
    float tmp, utilisation = 0.0, sumU = TARGET_UTILISATION, nextSumU, taskUtil;
    int i, valid_task_set = FALSE;
    unsigned int saved_seed = (unsigned) time (NULL);
    
    utilisation = 0.0;
    valid_task_set = TRUE;
    for (i = 0; i < NUM_TASKS; i++)
    {
        tasks[i].name[0] = (char) ((int) i/26)+'A';
        tasks[i].name[1] = (char) (i%26)+'A';
        tasks[i].name[2] = (char) 0;
        
        switch (HARMONIC_PERIODS)
        {
            case 0: tasks[i].period = log_rnd (MIN_PERIOD, MAX_PERIOD, PERIOD_STEP); break;
            case 1:
                switch (rnd (1,5,1))
            {
                case 1: tasks[i].period = 250000; break;
                case 2: tasks[i].period = 500000; break;
                case 3: tasks[i].period = 1000000; break;
                case 4: tasks[i].period = 2000000; break;
                case 5: tasks[i].period = 10000000; break;
                default: break;
            }
                break;
            default: break;
        }
        tasks[i].deadline = tasks[i].period;
        
        if (i != NUM_TASKS-1)
        {
            tmp = 1.0 / ((double) (NUM_TASKS - 1 - i));
            nextSumU = sumU * pow(((double) rand() / (RAND_MAX)), tmp);
            taskUtil = sumU - nextSumU;
        }
        else
            taskUtil = sumU;
        
        tasks[i].wcet = taskUtil * tasks[i].period;
        if (tasks[i].wcet <= 0)
            valid_task_set = FALSE;
        sumU = nextSumU;
        
        utilisation += (float) tasks[i].wcet / tasks[i].period;
        tasks[i].offset = 0;
        tasks[i].jitter = 0;
        tasks[i].priority = 0;
        tasks[i].affinity = rnd (0, MIN_PROCESSORS-1, 1);
    }
}

void copy_task_set (task *tasks, task *tasks_copy)
{
    int i;
    
    for (i=0; i< NUM_TASKS; i++)
        tasks_copy[i] = tasks[i];
}

int whole_schedulability_analysis (task *tasks, int OVERHEADS)
{
    task temp_tasks[NUM_TASKS][MAX_PROCESSORS], temp_tasks1[NUM_TASKS];
    int i, j, num_tasks_on_each_cpu[MAX_PROCESSORS];
    int unschedulable = 0;
    
    for (i=0; i<MAX_PROCESSORS;i++)
        num_tasks_on_each_cpu[i] = 0;
    for (i=0; i<NUM_TASKS; i++)
    {
        temp_tasks[num_tasks_on_each_cpu[tasks[i].affinity]][tasks[i].affinity] = tasks[i];
        num_tasks_on_each_cpu[tasks[i].affinity]++;
    }
    
    for (i=0; i<MAX_PROCESSORS;i++)
        if (num_tasks_on_each_cpu[i] != 0)
        {
            for (j=0; j<num_tasks_on_each_cpu[i]; j++)
                temp_tasks1[j] = temp_tasks[j][i];
            unschedulable += schedulability_analysis (temp_tasks1, num_tasks_on_each_cpu[i], OVERHEADS);
            if (DEBUG)
                printf ("For CPU %d, %d tasks unschedulable\n",
                        i, schedulability_analysis (temp_tasks1, num_tasks_on_each_cpu[i], OVERHEADS));
            for (j=0; j<num_tasks_on_each_cpu[i]; j++)
                temp_tasks[j][i] = temp_tasks1[j];
        }
    
    // put the tasks back
    for (i=0; i<NUM_TASKS; i++)
        for (j=0; j<num_tasks_on_each_cpu[tasks[i].affinity]; j++)
        {
            if (DEBUG)
                printf ("TEST %d %s, %d %s is ",i, tasks[i].name, j, temp_tasks[j][tasks[i].affinity].name);
            if (strcmp (tasks[i].name, temp_tasks[j][tasks[i].affinity].name) == 0)
                tasks[i] = temp_tasks[j][tasks[i].affinity];
            else
                if (DEBUG)
                    printf ("NOT ");
            if (DEBUG)
                printf ("a match\n");
        }
    
    return unschedulable;
}

float calculate_cost_function (task *tasks, const int overheads)
{
    float cost = 0.0;
    
    cost += whole_schedulability_analysis (tasks, overheads);
    
    cost /= NUM_TASKS;
    
    return cost;
}

void modify_function (task *tasks)
{
    int first_task = rnd (0, NUM_TASKS-1, 1), second_task = first_task, temp_priority, new_cpu = tasks[first_task].affinity;
    
    switch (rnd (1, TYPES_OF_MODIFY, 1))
    {
        case 1: // swap two tasks' priorities
            if (DEBUG)
                printf ("Swapped task's %d priority of %d ", first_task, tasks[first_task].priority);
            while (second_task == first_task)
                second_task = rnd (0, NUM_TASKS-1, 1);
            temp_priority = tasks[first_task].priority;
            tasks[first_task].priority = tasks[second_task].priority;
            tasks[second_task].priority = temp_priority;
            if (DEBUG)
                printf ("with task's %d priority of %d\n", second_task, tasks[first_task].priority);
            break;
        case 2: // move a task between CPUs
            if (DEBUG)
                printf ("Moved task %d from CPU %d ", first_task, tasks[first_task].affinity);
            while (tasks[first_task].affinity == new_cpu)
                new_cpu = rnd (0, MAX_PROCESSORS-1, 1);
            tasks[first_task].affinity = new_cpu;
            if (DEBUG)
                printf ("to CPU %d\n", new_cpu);
        default: break;
    }
}

int determine_number_of_processors (task *tasks)
{
    int i, num_cpus = 0, cpu_used[MAX_PROCESSORS];
    
    for (i=0; i<MAX_PROCESSORS; i++)
        cpu_used[i] = 0;
    for (i=0; i<NUM_TASKS; i++)
        cpu_used[tasks[i].affinity]++;
    
    for (i=0; i<MAX_PROCESSORS; i++)
        if (cpu_used[i] != 0)
            num_cpus++;
    
    return num_cpus;
}

void simulated_annealing (task *tasks, const int overheads)
{
    int i, no_of_moves_between_decisions = 0, no_of_moves = 0;
    task best_tasks[NUM_TASKS], current_tasks[NUM_TASKS];
    float current_value = 0, best_value = (float) INT_MAX, last_value = current_value, change_in_value = 0;
    int total_no_of_moves = 0, moves_since_last_best = 0, max_moves = INITIAL_MAX_MOVES;
    float temperature = INITIAL_TEMPERATURE, random_number;
    
    copy_task_set (tasks, current_tasks);
    copy_task_set (tasks, best_tasks);
    
    printf ("Move %d:", total_no_of_moves); fflush (stdout);
    current_value = calculate_cost_function (tasks, overheads);
    printf ("current value is %f, last value is %f, best_value is %f\n", current_value, last_value, best_value);
    
    do
    {
        do
        {
            if ((no_of_moves_between_decisions == 0) || (no_of_moves % no_of_moves_between_decisions) == 0)
                copy_task_set (current_tasks, tasks);
            modify_function (tasks);
            
            // calculate change in cost function value and then save new value
            printf ("Move %d:", total_no_of_moves+1); fflush (stdout);
            current_value = calculate_cost_function (tasks, overheads);
            printf ("current value is %f, last value is %f, best_value is %f\n", current_value, last_value, best_value);
            
            if ((max_moves == MAX_MOVES_SINCE_BEST) && INCREASE_PASSES_ON_SUCCESS)
            {
                if (whole_schedulability_analysis (best_tasks, overheads) == 0)
                    max_moves *= INCREASE_ON_SUCCESS;
            }
            
            if ((no_of_moves_between_decisions == 0)
                || (no_of_moves % no_of_moves_between_decisions) == 0)
            {
                last_value = current_value;
                change_in_value = current_value - last_value;
            }
            moves_since_last_best++;
            total_no_of_moves++;
            if (current_value < best_value)
            {
                moves_since_last_best = 0;
                best_value = current_value;
                copy_task_set (tasks, best_tasks);
            }
            
            // if improvement
            if (change_in_value < 0)
                // save the move as the current task set
                copy_task_set (tasks, current_tasks);
            else
            {
                // only give a random chance of accepting a solution
                // if the number of processors > minimum supposedly allowed
                if (determine_number_of_processors (tasks) >= MIN_PROCESSORS)
                {
                    // generate random number and see if greater than cooling function
                    random_number = (float) rand () / RAND_MAX;
                    if ((no_of_moves_between_decisions == 0) || (no_of_moves % no_of_moves_between_decisions) == 0)
                    {
                        if (change_in_value < 0)
                            if (random_number < exp (-change_in_value / temperature))
                                // if condition is met then keep the task set as current anyhow
                            {
                                // save the move as the current task set
                                copy_task_set (tasks, current_tasks);
                            }
                    }
                }
            }
            if (DEBUG)
                printf ("TEST: moves %d, moves since last best %d, max_moves %d\n", total_no_of_moves, moves_since_last_best, max_moves);
        }
        // evaluate N times, where N becomes bigger as temperature becomes smaller
        // That is, as we get closer to a solution we want to do more iterations
        while (no_of_moves++ < (MOVES_BETWEEN_COOLING * INITIAL_TEMPERATURE / temperature));
        
        // cool the temperature
        temperature *= (float) COOLING_FACTOR;
        no_of_moves = 0;
        
        // if we have had more than N moves since a best then try making current equal to best
        // that is, return the search to a sensible area
        if ((moves_since_last_best > (MAX_MOVES_SINCE_BEST / RESEED_FACTOR)) && (best_value > 0.0))
            copy_task_set (best_tasks, current_tasks);
    }
    // evaluate the number of moves since we last found a best one
    while (moves_since_last_best < max_moves);
    copy_task_set (best_tasks, tasks);
}


int main (void)
{
    task tasks[NUM_TASKS];
    int unschedulable;
    
    generate_task_set (tasks);
    if (HEADSTART_BY_DMPO)
        perform_dmpo (tasks, NUM_TASKS);
    
    if (DEBUG)
        printf ("Initial task set\n");
    if (DEBUG)
        print_task_set (tasks, NUM_TASKS);
    
    printf ("\nBefore optimisation: ");
    if (DEBUG)
        printf ("Schedulability analysis results without overheads\n");
    unschedulable = whole_schedulability_analysis (tasks, FALSE);
    if (DEBUG)
        print_task_set (tasks, NUM_TASKS);
    if (unschedulable == 0)
        printf ("Task set is schedulable\n");
    else
        printf ("Tasks set is unschedulable with %d missing their deadline\n", unschedulable);
    
    /*
     printf ("\nBefore optimisation: ");
     printf ("Schedulability analysis results with overheads\n");
     unschedulable = whole_schedulability_analysis (tasks, TRUE);
     if (DEBUG)
     print_task_set (tasks, NUM_TASKS);
     if (DEBUG)
     {
     if (unschedulable == 0)
     printf ("Task set is schedulable\n");
     else
     printf ("Tasks set is unschedulable with %d missing their deadline\n", unschedulable);
     }
     */
    
    simulated_annealing (tasks, FALSE);
    printf ("\nAfter optimisation: ");
    if (DEBUG)
        printf ("Schedulability analysis results without overheads\n");
    unschedulable = whole_schedulability_analysis (tasks, FALSE);
    if (DEBUG)
        print_task_set (tasks, NUM_TASKS);
    if (unschedulable == 0)
        printf ("Task set is schedulable\n");
    else
        printf ("Tasks set is unschedulable with %d missing their deadline\n", unschedulable);
    
    /*
     printf ("\n\nAll tasks sensitivity analysis results (with a multiplier) without overheads\n");
     sensitivity_analysis_all_tasks_multiplier (tasks, NUM_TASKS, FALSE);
     
     printf ("\n\nAll tasks sensitivity analysis results (with a multiplier) with overheads\n");
     sensitivity_analysis_all_tasks_multiplier (tasks, NUM_TASKS, TRUE);
     
     printf ("\n\nAll tasks sensitivity analysis results (a time unit at a time) without overheads\n");
     sensitivity_analysis_all_tasks (tasks, NUM_TASKS, FALSE);
     
     printf ("\n\nAll tasks sensitivity analysis results (a time unit at a time) with overheads\n");
     sensitivity_analysis_all_tasks (tasks, NUM_TASKS, TRUE);
     
     printf ("\n\nIndividual task sensitivity analysis results without overheads\n");
     sensitivity_analysis_individual_tasks (tasks, NUM_TASKS, FALSE);
     
     printf ("\n\nIndividual task sensitivity analysis results with overheads\n");
     sensitivity_analysis_individual_tasks (tasks, NUM_TASKS, TRUE);
     */
    
    return (0);
}
