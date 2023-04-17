# Evaluating Array and Bit Representation for Sequences

These experiment programs are designed to test the verification speed of a bit representation in comparison to a array representation.
The symbolic programs [``arrays.c``](arrays.c), [``bitShifts.c``](bitShifts.c) create an input state and then execute a single permutation action.
After the execution of the permutation action we can check for different properties of the resulting state:
```
tryPermutation()
```
For our experiment, we checked that for every sequence in the state, every probability was greater than 0. This ensured that we needed a lare permutation set size.

## Execution

The experimment can be performed by typing the following commands in a shell:
```
./runBitShiftTest.sh ARRAYS n '-D WEAK_SECURITY=k'
```
or
```
./runBitShiftTest.sh BITSHIFTS n '-D WEAK_SECURITY=k'
```
Through parameter **_n_** the number of cards can be specified.
The **WEAK_SECURITY** parameter **_n_** can have a value between 0 and 2.
The value **0** denotes probabilistic security, **1** denotes input-possibilistic security, and **2** denotes output-possibilistic security.

## Expanding to Symbolic Program that can Find Protocols

As stated before the experiment symbolic programs can not find a protocol.
However they contain a subset of the functions that make up the symbolic programs that find protocols.
They use the same structs as well.

The creation of the start state and shuffle action are almost completely implemented. 
Only some tests that (among other things) check for the security and correctness of a shuffle are still missing /e.g. **_isStillPossible()_**, **_combinePermutations()_**, **_isBottomFree()_**, **_checkTransitivityOfPermutation_**, ...).
The turn operation and its functions are not implemented jet (e.g. **_copyObservations()_**, **_applyTurn()_**, **_computeTurnProbabilities()_**, **_alignAndAssignFractions()_**, ...).
Further methods that are not implemented are the **isValid()** function, that checks whether a state is valid, i**nputProbability()** that checks if a sequence is an input sequence in the start state and **isFinalState()** that checks whether a certain state is a final state.
Instead of the **_tryPermutation()_** function, the symbolic programs that find protocols will have the **_perform Actions_** function, that will (up to a given bound) nondeterministically choose and execute an action.
The main() function is also also has to be slightly altered to create a symbolic program, that finds protocols.
