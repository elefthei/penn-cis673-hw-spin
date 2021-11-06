#define NTHREADS 2

bool queue[NTHREADS] = { 1, 0 };
bool crit[NTHREADS] = { 0, 0 };
byte cnt = 0;

/*
1. Initially, cnt is set to 0 and queue is all 0s except for the first cell which is set to 1.

2. Each process first atomically gets and then increments cnt and stores its current value locally.
3. Then it waits until the position indicated by cnt in the queue is set to true (modulo NTHREADS, i.e., val % NTHREADS). 
    - When its cell is set to true, it enters the critical section
    - Sets its index in the queue to false
    - Sets the next cell in the queue array to true (passing control to the next process).

4. The processes should do the above steps in an infinite loop, continuously trying to access the critical section.
*/
active [NTHREADS] proctype process() {
    byte state = 0;
    byte localcnt;
    do
    :: (state == 0) -> atomic {
          localcnt = cnt % NTHREADS;
          cnt++;
          state = 1;
    }
    :: (state == 1) -> (queue[localcnt] == true) -> atomic {
            crit[_pid] = 1;
            queue[localcnt] = false;
            queue[(localcnt+1) % NTHREADS] = true;
            state = 0;
            crit[_pid] = 0;
    }
    od
}

/*
1. mutual exclusion in the critical section, i.e., only a single process is at the critical section at any time;
2. flag slots are used in order; and
3. starvation-freedom, i.e., a process that tries to enter the critical section will eventually enter (you might need to manually refer to all threads one by one for checking starvation freedom, meaning that your code for checking it might not be parametric with respect to NTHREADS).
*/
ltl invariant { 
    [] !(crit[0] && crit[1]) &&        // Mutual exclusion of critical sections
    [] !(queue[0] && queue[1]) &&      // Mutual exclusion of queue slots
    [] (queue[0] -> (<> queue[1])) &&  // In-order queueing (0)
    [] (queue[1] -> (<> queue[0])) &&  // In-order queueing (1)
    [] (<> queue[0]) &&                // Starvation freedom (0)
    [] (<> queue[1])                   // Starvation freedom (1)
}