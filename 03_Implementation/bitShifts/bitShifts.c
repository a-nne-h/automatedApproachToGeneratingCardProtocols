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
struct sequence {
    unsigned int val[N];
    struct fractions probs;
};


/**
 * All sequences are remembered here, as seen from left to right, sorted alphabetically.
 * The states in this program are equal to the states in KWH trees.
 */
struct state {
    struct sequence seq[NUMBER_POSSIBLE_SEQUENCES];
};

/**
 * All permutations are remembered here, as seen from left to right, sorted alphabetically.
 */
struct permutationState {
    struct sequence seq[NUMBER_POSSIBLE_PERMUTATIONS];
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
            s.seq[i].val[j] = nondet_uint();
            unsigned int val = s.seq[i].val[j];
            assume(0 < val && val <= N);
            unsigned int idx = val - 1;
            assume(!taken.arr[idx]);
            taken.arr[idx]++;
        }
    }

    // Not needed, but to avoid state space explosion
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_PERMUTATIONS; i++) {
        for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
            s.seq[i].probs.frac[j].num = 0;
            s.seq[i].probs.frac[j].den = 1;
        }
    }

    for (unsigned int i = 1; i < NUMBER_POSSIBLE_PERMUTATIONS; i++) {
        unsigned int checked = 0;
        unsigned int last = i - 1;
        for (unsigned int j = 0; j < N; j++) {
            // Check lexicographic order
            unsigned int a = s.seq[last].val[j];
            unsigned int f = s.seq[i].val[j];
            checked |= (a < f);
            assume(checked || a == f);
        }
        assume(checked);
    }
    return s;
}

int main() {
    stateWithAllPermutations = getStateWithAllPermutations();
    unsigned int index = nondet_uint();
    unsigned int val = nondet_uint();
    assume(val < N);
    assume(index < NUMBER_POSSIBLE_SEQUENCES);
    assert(stateWithAllPermutations.seq[index].val[val] != 0);
    return 0;
}