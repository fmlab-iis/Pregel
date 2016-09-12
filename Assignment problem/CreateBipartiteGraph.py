import sys
import random
from munkres import Munkres, print_matrix 
import time

start = time.time()
n = input('Please input a positive integer N\n')
print(n)
# PersonID 1~N ObjectID N+1~2N
f = open('Edge.csv', 'w')
N=int(n)
matrix = []
for person in range(1,N+1):
    temp =[]
    for obj in range(N+1,2*N+1):
    	randnum = random.randint(0,50)
	f.write('%d,%d,%d\n' % (person,obj,randnum))
        temp.append(randnum+1)
    matrix.append(temp)

#print matrix
f.close()

cost_matrix = []

for row in matrix:
    cost_row=[]
    for col in row:
        cost_row+=[sys.maxsize- col]
    cost_matrix += [cost_row]



m = Munkres()
indexes = m.compute(cost_matrix)
print_matrix(matrix, msg='Highest profit through this matrix:')
total = 0
for row, column in indexes:
    value = matrix[row][column]
    total += value
    #print '(%d, %d) -> %d' % (row, column, value)

print 'total profit=%d' % (total-N)

end = time.time()
print(end-start)
