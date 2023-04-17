## Execution
These programs can be executed as followed:
The command is 
```
./runTwoCard.sh booleanOperator n l 
```
where booleanOperator is the operator for which a protocol is to be found, (currently supported: AND, OR, XOR, COPY)
n is the number of cards
and l is the number of steps.

There are two .out files produced, one with the complete trace and one with a shorter trace, that contains the essential information needed for constructing the KWH-Trees.

## Possible configurations
Additionally to parameters present in the original programs (e.g. **WEAK_SECURITY**, **FINITE_RUNTIME**,...), we can also decide if and what protocols we want to use as operations.
* **MODULES** determines whether protocols are used as operations (**1**) or we only use shuffle and turn operations (**0**).
* The parameters **USE_FR_AND**, **USE_FR_XOR**, **USE_LV_AND**, **USE_LV_OR** and **USE_FR_COPY** decide whether a specific protocol will be considered as an operation. **1** signifies a protocol being used, **0** signifies a protocol not being used. For description and sources of the protocols being used, please see [``modules.c``](modules.c)

You can use the parameters by appending the following (do not omit the quotation marks) for each of the options (**MODE** stands for the keyword and **PARAMETER** for the value):

```
'-D MODE=PARAMETER'
```
