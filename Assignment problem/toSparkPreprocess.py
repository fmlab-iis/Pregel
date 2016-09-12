import sys
graph = open('Edge.csv','r')
personVD = open('PersonVertex.csv', 'w')
objectVD = open('ObjectVertex.csv', 'w')
selfEdge = open('SelfPersonEdge.csv', 'w')

firstline = graph.readline().split(",")
N = int(firstline[1])-int(firstline[0])
graph.close()
for index in range(1,N+1):
    personVD.write('%d\n' % (index))
    selfEdge.write('%d,%d,0\n' % (index,index))

for index in range(N+1, 2*N+1):
    objectVD.write('%d\n' % (index))

personVD.close()
objectVD.close()
selfEdge.close()


