# SGAC-Z3py

The tests may be found in the folder Tests.

For each changing parameter we have test sets inside the folder with the same name. We also group the tests for the same variable in a folder. 
For example, changing the number of contexts, we have tests for 10, 20 and 30 contexts. The group of tests for 10 different contexts may be found on 10contexts folder.

Alloy tests are available separately inside a folder named alloy followed by a number indicating the test number. For example, alloy1 inside 10contexts folder contains the first test set with 10contexts. 
ProB machines are available directly on the folder. For example, inside 10contexts folder we find SGAC_B_1.mch which contains the first machine for test with 10contexts.
Z3 specifications are avaible directly on the folder. For example, inside 10contexts folder there is SGAC_Z3_1_MODEL1.txt which contains the first stage for the Z3 model. The next stage for the model may be found while adding one to the last digit. So the second stage is SGAC_Z3_1_MODEL2.txt.

The folder also contain a file SGAC_random_number.text where number varies from one to the number of experiments. It contains the random generated dataset.

The results for running an experiment are found in the test folder as a xlsx file.

To run the tests:

For Alloy the plotted time is the time alloy takes to solve all the properties. So since we have 4 properties and 1 alloy file for each property, the time alloy takes to solve the 4 properties is the sum of each alloy file(reqNumber.als inside access, contexts, hidden, and ineffective folder). For each different request, alloy will create a different group of files (graph_number).

For ProB we pass the file to probcli and ask it initialize the machine. So it is going to set the constants and initialize the machine. That is the time ProB takes to check all the four properties.

For Z3 it is necessary to run sgac_random_number.text with the python file SGAC.py sending three parameters. 1) The test name. 2) the directory where we can found the sgac_random_number.text document and 3) the number of the random test.



