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
 * Size of input sequence (number of cards including both commitments plus additional cards).
 */
#ifndef N
#define N 4
#endif

 /**
  * Maximum number of sequences (usually N!).
  * This value can be lowered if there are multiple indistinguishable symbols in the deck.
  * This variable is used for over-approximating loops such that
  * their unrolling bound can be statically determined.
  */
#ifndef NUMBER_POSSIBLE_SEQUENCES
#define NUMBER_POSSIBLE_SEQUENCES 24
#endif

 /**
  * Maximum number of permutations fpr the given number of cards (N!).
  * This value has to be computed by our script, or adjusted manually.
  */
#ifndef NUMBER_POSSIBLE_PERMUTATIONS
#define NUMBER_POSSIBLE_PERMUTATIONS 24
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
 * An integer array with length N.
 */
struct narray {
    unsigned int arr[N];
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

/**
 * Given an array containing a sequence, we return the index of the given sequence in a state.
 */
unsigned int getSequenceIndexFromArray(struct narray compare, struct state compareState) {
    unsigned int seqIdx = nondet_uint();
    assume(seqIdx < NUMBER_POSSIBLE_SEQUENCES);
    struct sequence seq = compareState.seq[seqIdx];

    for (unsigned int i = 0; i < N; i++) {
        assume(compare.arr[i] == seq.val[i]);
    }
    return seqIdx;
}

/**
 * Update the possibilities of a sequence after a shuffle.
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

// emptyState; (isStillPossible);
/**
 * Calculate the state after a shuffle operation starting from s with the given permutation set.
 * 
 * Deleted isStillPossible
 */
struct state doShuffle(struct state s,
    unsigned int permutationSet[MAX_PERM_SET_SIZE][N],
    unsigned int permSetSize) {
    struct state res = emptyState;
    // For every sequence in the input state.
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
            // For every permutation in the permutation set.
            for (unsigned int j = 0; j < MAX_PERM_SET_SIZE; j++) {
                if (j < permSetSize) {
                    struct narray resultingSeq = { .arr = { 0 } };
                    for (unsigned int k = 0; k < N; k++) {
                        // Apply permutation j to sequence i.
                        resultingSeq.arr[permutationSet[j][k]] = s.seq[i].val[k];
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
                permutationSet[i][j] = stateWithAllPermutations.seq[permIndex].val[j] - 1;
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