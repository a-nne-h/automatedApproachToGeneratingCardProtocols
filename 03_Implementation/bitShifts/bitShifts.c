//    This program is free software; you can redistribute it and/or modify
//    it under the terms of the GNU General Public License as published by
//    the Free Software Foundation; either version 3 of the License, or
//    (at your option) any later version.

//    This program is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//    GNU General Public License for more details.

//    You should have received a copy of the GNU General Public License
//    along with this program; if not, <http://www.gnu.org/licenses/>.

#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

unsigned int nondet_uint();
void __CPROVER_assume(int x);
void __CPROVER_assert(int x, char y[]);

#define assert2(x, y) __CPROVER_assert(x, y)
#define assume(x) __CPROVER_assume(x)

/**
 * Amount of distinguishable card symbols.
 */
#ifndef NUM_SYM
#define NUM_SYM 2
#endif

 /**
  * Size of input sequence (number of cards including both commitments plus additional cards).
  */
#ifndef N
#define N 4
#endif

  /**
   * Number of all cards used for commitments
   */
#ifndef COMMIT
#define COMMIT 4
#endif

   /**
    * Maximum number of sequences (usually N!).
    * This value can be lowered if there are multiple indistinguishable symbols in the deck.
    * This variable is used for over-approximating loops such that
    * their unrolling bound can be statically determined.
    */
#ifndef NUMBER_POSSIBLE_SEQUENCES
#define NUMBER_POSSIBLE_SEQUENCES 6
#endif

    /**
     * For two players inserting yes or no to a protocol,
     * there are four different possibilities how the protocol could start.
     * For more players or other scenarios this value has to be adapted.
     */
#ifndef NUMBER_START_SEQS
#define NUMBER_START_SEQS 4
#endif


     /**
      * Maximum number of permutations fpr the given number of cards (N!).
      * This value has to be computed by our script, or adjusted manually.
      */
#ifndef NUMBER_POSSIBLE_PERMUTATIONS
#define NUMBER_POSSIBLE_PERMUTATIONS 24
#endif


      /**
       * Regarding possibilities for a sequence, we (only) consider
       * - 0: probabilistic security
       *      (exact possibilities for a sequence)
       * - 1: input possibilistic security (yes or no)
       *      (whether the sequence can belong to the specific input)
       * - 2: output possibilistic security (yes or no)
       *      (to which output the sequence can belong)
       */
#ifndef WEAK_SECURITY
#define WEAK_SECURITY 2
#endif


       /**
        * We always had four input possibilities,
        * this is changed if we only consider output possibilistic security.
        * This variable is used for over-approximating loops such that
        * their unrolling bound can be statically determined.
        */
#if WEAK_SECURITY == 2
#define NUMBER_PROBABILITIES 2
#else
#define NUMBER_PROBABILITIES 4
#endif

        /**
         * This variable is used to limit the permutation set in any shuffle.
         * This can reduce the running time of this program.
         * When reducing this Variable, keep in mind that it could exclude some valid protocols,
         * as some valid permutation sets are not longer considered.
         */
#ifndef MAX_PERM_SET_SIZE
#define MAX_PERM_SET_SIZE NUMBER_POSSIBLE_PERMUTATIONS
#endif

struct fraction {
    unsigned int num; // The numerator.
    unsigned int den; // The denominator.
};

struct fractions {
    struct fraction frac[NUMBER_PROBABILITIES];
};

/**
 * This is one sequence, as seen from left to right.
 *
 * If the sequence can belong to a specific input sequence,
 * then the probabilities entry is set to the probability for this input sequence.
 * Indices:
 * - 0: X_00
 * - 1: X_01
 * - 2: X_10
 * - 3: X_11
 *
 * If the sequence is not contained in the state, all probabilities are set to zero.
 *
 * We save the probabilities as numerator/denominator (of type fraction),
 * so we can avoid floating point operations and divisions.
 *
 * One line looks like this:
 *   val:           [card#1][card#2]..[card#N]
 *   probs:         [num#1]..[num#4]
 *   (num./denom.)  [den#1]..[den#4]
 *
 * For input-possibilistic protocols,
 * we only need to determine whether a sequence can belong to a specific input:
 *    [card#1][card#2]..[card#N]
 *    [bool#1]..[bool#4]
 *
 * For output-possibilistic protocols,
 * we only need to determine whether a sequence can belong to a specific output:
 *    [card#1][card#2]..[card#N]
 *    [bool#1][bool#2]
 * Note that in this scenario, we have bool#1 == X_0 and bool#2 == X_1.
 */
/**
* BITSHIFTS:
* value as a char
*/
struct sequence {
    char val;
    struct fractions probs;
};


/**
 * All sequences are remembered here, as seen from left to right, sorted alphabetically.
 * The states in this program are equal to the states in KWH trees.
 */
struct state {
    struct sequence seq[NUMBER_POSSIBLE_SEQUENCES];
};

struct permSequence {
    unsigned int val[N];
    struct fractions probs;
};

/**
 * All permutations are remembered here, as seen from left to right, sorted alphabetically.
 */
struct permutationState {
    struct permSequence permSeq[NUMBER_POSSIBLE_PERMUTATIONS];
};

/**
 * We store all possible permutations into a seperate state to save resources.
 */
struct permutationState stateWithAllPermutations;

/**
 * We store one empty state at beginning of the program to save ressources.
 */
struct state emptyState;

/**
 * An integer array with length N.
 */
struct narray {
    unsigned int arr[N];
};

/**
 * An integer array with length NUM_SYM.
 */
struct numsymarray {
    unsigned int arr[NUM_SYM];
};



struct permutationState getStateWithAllPermutations() {
    struct permutationState s;
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_PERMUTATIONS; i++) {
        struct narray taken;
        for (unsigned int j = 0; j < N; j++) {
            taken.arr[j] = 0;
        }
        for (unsigned int j = 0; j < N; j++) {
            s.permSeq[i].val[j] = nondet_uint();
            unsigned int val = s.permSeq[i].val[j];
            assume(0 < val && val <= N);
            unsigned int idx = val - 1;
            assume(!taken.arr[idx]);
            taken.arr[idx]++;
        }
    }

    // Not needed, but to avoid state space explosion
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_PERMUTATIONS; i++) {
        for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
            s.permSeq[i].probs.frac[j].num = 0;
            s.permSeq[i].probs.frac[j].den = 1;
        }
    }

    for (unsigned int i = 1; i < NUMBER_POSSIBLE_PERMUTATIONS; i++) {
        unsigned int checked = 0;
        unsigned int last = i - 1;
        for (unsigned int j = 0; j < N; j++) {
            // Check lexicographic order
            unsigned int a = s.permSeq[last].val[j];
            unsigned int f = s.permSeq[i].val[j];
            checked |= (a < f);
            assume(checked || a == f);
        }
        assume(checked);
    }
    return s;
}


/**
 * Given an char containing a sequence, we return the index of the given sequence in a state.
 */
/**
* BITSHIFTS:
* we have a char instead of an array for comparison
*/
unsigned int getSequenceIndexFromArray(char compare, struct state compareState) {
    unsigned int seqIdx = nondet_uint();
    assume(seqIdx < NUMBER_POSSIBLE_SEQUENCES);
    struct sequence seq = compareState.seq[seqIdx];
    assume(!(seq.val ^ compare)); // the chars are equal if XOR is 0 
    return seqIdx;
}

/**
 * Update the possibilities of a sequence after a shuffle.
 */
 /**
 * BITSHIFTS:
 * stayed the same, because only the probs are touched
 */
struct fractions recalculatePossibilities(struct fractions probs,
    struct fractions resProbs,
    unsigned int permSetSize) {
    for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
        struct fraction prob = probs.frac[k];
        unsigned int num = prob.num;
        unsigned int denom = prob.den;

        if (num && WEAK_SECURITY) {
            resProbs.frac[k].num |= num;
        }
        else if (num) {
            /**
             * Only update fractions in case we are in the
             * strong security setup.
             */
             // Update denominator.
            resProbs.frac[k].den = denom * permSetSize;
            // Update numerator.
            resProbs.frac[k].num = (num * permSetSize) + denom;
        }
    }
    return resProbs;
}


/**
 * Calculate the state after a shuffle operation starting from s with the given permutation set.
 *
 * Deleted isStillPossible
 */
/**
* BITSHIFTS:
* changed content in 2nd for loop, especially the application of the permutatuin to the sequence
*/
struct state doShuffle(struct state s,
    unsigned int permutationSet[MAX_PERM_SET_SIZE][N],
    unsigned int permSetSize) {
    struct state res = emptyState;
    // For every sequence in the input state.
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        struct sequence seq = s.seq[i];
        // For every permutation in the permutation set.
        for (unsigned int j = 0; j < MAX_PERM_SET_SIZE; j++) {
            if (j < permSetSize) {
                char resultingSeq = 0;
                for (unsigned int k = 0; k < N; k++) {
                    // Apply permutation j to sequence i.
                    char temp = seq.val & (1 << k);
                    temp = temp << (permutationSet[j][k] - k);
                    resultingSeq = resultingSeq | temp;
                }
                unsigned int resultSeqIndex = // Get the index of the resulting sequence.
                    getSequenceIndexFromArray(resultingSeq, res);
                // Recalculate possibilities.
                res.seq[resultSeqIndex].probs =
                    recalculatePossibilities(s.seq[i].probs,
                        res.seq[resultSeqIndex].probs,
                        permSetSize);
            }
        }
    }
    return res;
}

struct state applyShuffle(struct state s) {
    // Generate permutation set (shuffles are assumed to be uniformly distributed).
    unsigned int permSetSize = nondet_uint();
    assume(0 < permSetSize && permSetSize <= MAX_PERM_SET_SIZE);
    
    unsigned int permutationSet[MAX_PERM_SET_SIZE][N] = { 0 };
    unsigned int takenPermutations[NUMBER_POSSIBLE_PERMUTATIONS] = { 0 };
    /**
     * Choose permSetSize permutations nondeterministically. To achieve this,
     * generate a nondeterministic permutation index and get the permutation from this index.
     * No permutation can be chosen multiple times.
     */
    unsigned int lastChosenPermutationIndex = 0;
    for (unsigned int i = 0; i < MAX_PERM_SET_SIZE; i++) {
        if (i < permSetSize) { // Only generate permutations up to permSetSize.
            unsigned int permIndex = nondet_uint();
            // This ensures that the permutation sets are sorted lexicographically.
            assume(lastChosenPermutationIndex <= permIndex);
            assume(permIndex < NUMBER_POSSIBLE_PERMUTATIONS);
            assume(!takenPermutations[permIndex]);

            takenPermutations[permIndex] = 1;
            lastChosenPermutationIndex = permIndex;

            for (unsigned int j = 0; j < N; j++) {
                permutationSet[i][j] = stateWithAllPermutations.permSeq[permIndex].val[j] - 1;
                /**
                 * The '-1' is important. Later, we convert to array indices such as
                 * array[permutationSet[x][y]]. Without the '-1', we would get out-
                 * of-bound errors there.
                 */
            }
        }
    }
    struct state res = doShuffle(s, permutationSet, permSetSize);
    return res;
}

struct state tryPermutation(struct state s) {
    struct state res = applyShuffle(s);
   
    // check if every possibility is 1 after shuffle
    for (int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        for (int j = 0; j < NUMBER_PROBABILITIES; j++) {
            assume(res.seq[i].probs.frac[j].num == 0);
        }
    }
    return s;
}



/**
 * Constructor for states. Only use this to create new states.
 */
struct state getEmptyState() {
    struct state s;
    struct numsymarray symbolCount;
    for (unsigned int i = 0; i < NUM_SYM; i++) {
        symbolCount.arr[i] = 0;
    }
    
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        struct numsymarray taken;
        for (unsigned int j = 0; j < NUM_SYM; j++) {
            taken.arr[j] = 0;
        }

        //s.seq[i].val = nondet_uint();
        char value = 0;
        for (unsigned int j = 0; j < N; j++) {
            char val = nondet_uint();
            assume(0 <= val && val <= 1);
            taken.arr[val]++;
            assume(taken.arr[val] <= N - 2); // At least two symbols have to be different. Players cannot commit otherwise.
            value = value | (val << (N - 1 - j));
        }
        s.seq[i].val = value;
        
        for (unsigned int j = 0; j < NUM_SYM; j++) {
            if (i == 0) {
                symbolCount.arr[j] = taken.arr[j];
            }
            else { // We ensure that every sequence consists of the same symbols
                assume(taken.arr[j] == symbolCount.arr[j]);
            }
        }

        // Here we store the numerators and denominators
        for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
            s.seq[i].probs.frac[j].num = 0;
            s.seq[i].probs.frac[j].den = 1;
        }
    }
    for (unsigned int i = 1; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        unsigned int checked = 0;
        unsigned int last = i - 1;
        for (unsigned int j = 1; j <= N; j++) {
            // Check lexicographic order
            char a = (s.seq[last].val & (1 << N - j));
            char f = (s.seq[i].val & (1 << N - j));
            checked |= (a < f);
            assume(checked || a == f);
        }
        assume(checked);
    }
    return s;
}

// isZero
// isOne

/**
 * Determine if a sequence in the start state belongs to the input possibility (0 0).
 */

unsigned int isZeroZero(char sequence) {
    if(sequence & (1 << (N - 1))) {
        return 0;
    }
    if (!(sequence & (1 << (N - 2)))) {
        return 0;
    }
    if (sequence & (1 << (N - 3))) {
        return 0;
    }
    if (!(sequence & (1 << (N - 4)))) {
        return 0;
    }
    return 1;
}

/**
 * Determine if a sequence in the start state belongs to the input possibility (1 1).
 */
unsigned int isOneOne(char sequence) {
    if (!(sequence & (1 << (N - 1)))) {
        return 0;
    }
    if (sequence & (1 << (N - 2))) {
        return 0;
    }
    if (!(sequence & (1 << (N - 3)))) {
        return 0;
    }
    if (sequence & (1 << (N - 4))) {
        return 0;
    }
    return 1;
}



/**
 * This method constructs the start sequence for a given commitment length COMMIT
 * using nodeterministic assignments. We only consider the case where Alice uses
 * the cards "1" and "2", and Bob uses the cards "3" and "4".
 */
char getStartSequence() {
    assume(N >= COMMIT); // We assume at least as many cards as needed for the commitments.
    struct numsymarray taken;
    for (unsigned int i = 0; i < NUM_SYM; i++) {
        taken.arr[i] = 0;
    }
    char res = 0;
    for (unsigned int i = 0; i < COMMIT; i++) {
        char card = nondet_uint();
        assume(0 <= card && card < COMMIT && card < NUM_SYM);
        assume(taken.arr[card] < COMMIT / NUM_SYM);
        taken.arr[card]++;
        res = res | (card << (N - 1 - i));
    }
    // Here we assume that each player only uses fully distinguishable cards
    assume((res & 1 << (N - 1)) != ((res & 1 << (N - 2))<<1));
    assume((res & 1 << (N - 3)) != ((res & 1 << (N - 4)) << 1));

    // rest of cards
    for (unsigned int i = COMMIT; i < N; i++) {
        char card = nondet_uint();
        assume(0 <= card);
        assume(card < NUM_SYM);
        res = res | (card << (N - 1 - i));
    }
    return res;
}




int main() {
    emptyState = getEmptyState();
    struct state startState = emptyState;  
    char start[NUMBER_START_SEQS];
    for (unsigned int i = 0; i < NUMBER_START_SEQS; i++) {
        start[i] = getStartSequence();
    }
    //assume(isZeroZero(start[0]));

    assume(isZeroZero(start[0]));

    assume(!((start[0] & (1 << N - 1)) ^ (start[1] & (1 << N - 1))));
    assume((start[1] & (1 << N - 1)) ^ (start[2] & (1 << N - 1)));
    assume(!((start[2] & (1 << N - 1)) ^ (start[3] & (1 << N - 1))));

    assume(!((start[0] & (1 << N - 3)) ^ (start[2] & (1 << N - 3))));
    assume((start[0] & (1 << N - 3)) ^ (start[1] & (1 << N - 3)));
    assume(!((start[1] & (1 << N - 3)) ^ (start[3] & (1 << N - 3))));

    unsigned int arrSeqIdx[NUMBER_START_SEQS];
    for (unsigned int i = 0; i < NUMBER_START_SEQS; i++) {
        arrSeqIdx[i] = getSequenceIndexFromArray(start[i], startState);
    }

    for (unsigned int i = 0; i < (NUMBER_START_SEQS - 1); i++) {
        startState.seq[arrSeqIdx[i]].probs.frac[0].num = 1;
    }

    unsigned int lastStartSeq = NUMBER_START_SEQS - 1;
    unsigned int arrIdx = arrSeqIdx[lastStartSeq];
    unsigned int lastProbIdx = NUMBER_PROBABILITIES - 1;
    startState.seq[arrIdx].probs.frac[lastProbIdx].num = isOneOne(start[lastStartSeq]);

    stateWithAllPermutations = getStateWithAllPermutations();

    tryPermutation(startState);
    //tryPermutations ()
    assert(0);
    return 0;
}