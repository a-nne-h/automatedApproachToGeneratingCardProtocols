import sys
import re
patternNL = r'\r?\n'

f = open(sys.argv[1], "r+")
content = str(f.read())
list = content.splitlines()
newlist=[]
rest = []
for item in list:
    if  re.match("[0-9]", item):
        newlist.append(re.split(":|-", item, maxsplit=1))
    else:
        rest.append(item)
for i in range(0,len(newlist)):
    newlist[i][0] = int(newlist[i][0])
newlist.sort()

string = str("")
for item in rest :
    string = string + item
    string = string + "\n"
for item in newlist:
    for element in item:
        element = str(element)
        string = string + element
    string = string + "\n"

with open(sys.argv[1],'w') as g:
    g.write(string)
