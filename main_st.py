from pysat.formula import CNF
from pysat.solvers import Solver
from pysat.card import *
from sympy import symbols, Or, And, Not, to_cnf
from sympy.logic import false
from collections import deque
from copy import deepcopy
from itertools import product
from pysat.card import ITotalizer
from itertools import combinations
import numpy as np
from astar_cnf import astar_CNF
from backtrack_cnf import back_track
from brute_force_cnf import brute_force
from helper_function import all_true_clauses, assignment_to_model, fill_value_to_unit_clauses, select_most_frequent_variable, contain_false_clause, get_variables


Moves=[[-1,0],[0,-1],[1,0],[0,1]]
      
class Hashiwokakero_Grids:
    def __init__(self):
        self.islands_count=0
        self.is_numth={}
        filename="input.txt"
        with open(filename,'r',encoding='utf-8') as file:
            self.range=int(file.readline().strip())
            self.grid = [[0] * self.range for _ in range(self.range)]
            for i in range(self.range):
                line=file.readline()
                parts=line.split()
                for j in range(len(parts)):
                    self.grid[i][j]=int(parts[j])
                    if (self.grid[i][j]!=0):
                        self.is_numth[(i,j)]=self.islands_count
                        self.islands_count+=1
        self.min_index=4*self.islands_count+1
        self.posxy = [None] * self.islands_count
        count=0
        for i in range(self.range):
            for j in range(self.range):
                if self.grid[i][j]!=0:
                    self.posxy[count]=i,j
                    count+=1
        self.edges=[None]*self.min_index
        self.num_edge=0
        self.limit_range=[[0]*9 for _ in range(9)]
        self.limit = {}
        for ri11 in range(2):
            for ri12 in range(ri11+1):
                if (ri11==0): i11=-1
                else: i11=1
                if (ri12==0): i12=-1
                else: i12=1
                temp1=[i11,i12]
                self.limit[(2,ri11+ri12,self.limit_range[2][ri11+ri12])]=temp1
                self.limit_range[2][ri11+ri12]+=1
                for ri21 in range(2):
                    for ri22 in range(ri21+1):
                        if (ri21==0): i21=-1
                        else: i21=1
                        if (ri22==0): i22=-1
                        else: i22=1
                        temp2=[i11,i12,i21,i22]
                        self.limit[(4,ri11+ri12+ri21+ri22,self.limit_range[4][ri11+ri12+ri21+ri22])]=temp2
                        self.limit_range[4][ri11+ri12+ri21+ri22]+=1
                        for ri31 in range(2):
                            for ri32 in range(ri31+1):
                                if (ri31==0): i31=-1
                                else: i31=1
                                if (ri32==0): i32=-1
                                else: i32=1
                                temp3=[i11,i12,i21,i22,i31,i32]
                                self.limit[(6,ri11+ri12+ri21+ri22+ri31+ri32,self.limit_range[6][ri11+ri12+ri21+ri22+ri31+ri32])]=temp3
                                self.limit_range[6][ri11+ri12+ri21+ri22+ri31+ri32]+=1
                                for ri41 in range(2):
                                    for ri42 in range(ri41+1):
                                        if (ri41==0): i41=-1
                                        else: i41=1
                                        if (ri42==0): i42=-1
                                        else: i42=1
                                        temp4=[i11,i12,i21,i22,i31,i32,i41,i42]
                                        self.limit[(8,ri11+ri12+ri21+ri22+ri31+ri32+ri41+ri42,self.limit_range[8][ri11+ri12+ri21+ri22+ri31+ri32+ri41+ri42])]=temp4
                                        self.limit_range[8][ri11+ri12+ri21+ri22+ri31+ri32+ri41+ri42]+=1
        

    #Đổi quan hệ của 2 đảo sang mệnh đề index, ở đây ta chỉ xét index bằng vị trí hòn đảo gần với (0,0), hướng xây cầu và số lượng cầucầu
    def To_index(self,x1,y1,x2,y2,d):
        x,y=x1,y1
        if (x2<x1 or y2<y1):
            x1,x2=x2,x
            y1,y2=y2,y
        #c là biến để nếu lên hướng câu
        #c=0 là cầu dọc
        # c=1 là cầu ngang 
        if (x1==x2): c=1
        else: c=0
        #d là số cầu:0,1,2
        return (self.is_numth[(x1,y1)]) * 4+2*c+d+1

    #Kiểm tra vị trí đảo có tồn tại không 
    def isValid(self,x,y):
        if (x<0): return False
        if (y<0): return False
        if (x>=self.range): return False
        if (y>=self.range): return False
        return True
    

    #Tìm island gần nhất của island đang xét theo hướng        
    # Trên nếu direct=0
    # TRái nếu direct=1
    # Dưới nếu direct=2
    # Phải nếu direct=3 
    #Request_2,Request_3: Khống chế hướng hàng xóm của đảo chỉ còn theo chiều dọc và chiều ngang và không qua các đảo
    def Neightbour(self,x,y,direct):
        dx,dy=Moves[direct]
        Next_x,Next_y=x+dx,y+dy
        while self.isValid(Next_x,Next_y):
            if self.grid[Next_x][Next_y]!=0: return Next_x,Next_y
            Next_x,Next_y=Next_x+dx,Next_y+dy
        return -1,-1
    
    
    def Request_2(self):#Hai cây cầu không được xây qua nhau
        #Ta sẽ tìm kiếm nhưng cầu dọc có thể xây, mỗi khi tìm được 1 cây cầu dọc ta sẽ tìm những cây câu ngang xây đi qua cây cầu dọc đó và thêm điều kiện
        clauses=[]
        temp=[]
        for i1 in range(self.range):
            for j1 in range(self.range):
                #Tìm đảo 
                if (self.grid[i1][j1]!=0):
                    #Tìm cầu dọc
                    n_i1,n_j1=self.Neightbour(i1,j1,2)
                    if (n_i1==-1 or n_j1==-1): continue 
                    else:
                        #Tìm các đảo bên trái cầu dọc
                        for between in range(i1+1,n_i1):
                            i2,j2=self.Neightbour(between,j1,1)
                            if (i2==-1 or j2==-1): continue
                            else:
                                #Liệt kê các cầu gây xung đột cho cầu dọc 
                                i3,j3=self.Neightbour(i2,j2,3)
                                if (i3==-1 or j3==-1): continue
                                else:
                                    #Thêm mệnh đề: nếu cầu dọc tồn tại =>cầu ngang được tìm ra không tồn tại 
                                    temp.append(-1*self.To_index(i1,j1,n_i1,n_j1,0))
                                    temp.append(-1*self.To_index(i2,j2,i3,j3,0))
                                    clauses.append(temp)
                                    temp=[]
        return clauses

    def Request_4(self):#giữa hai hòn đảo chỉ có tối đa 2 cây cầu
        #Ta sẽ tìm 2 đảo có thể xây cầu rồi gọi 
        #Index1 là sự tồn tại của cây cầu thứ 1 giữa 2 đảo
        #Index2 là sự tồn tại của cây cầu thứ 2 giữa 2 đảo
        #Khi đó: Index2 chỉ tồn tại nếu Index 1 tồn tại, tức là nếu giữa 2 đảo chỉ có một cầu thì cầu đó là Index1: Index2=>Index1
        #Index1 and INdex 2 đúng tức là giữa đảo có 2 cầu
        clauses=[]
        temp=[]
        for i in range(self.range):
            for j in range(self.range):
                if (self.grid[i][j]!=0):
                    for c in range(2,4):
                        ni,nj=self.Neightbour(i,j,c)
                        if (ni==-1 or nj==-1): continue
                        else:
                            #Index2=>Index1
                            temp.append(-1*self.To_index(i,j,ni,nj,1))
                            temp.append(self.To_index(i,j,ni,nj,0))
                            clauses.append(temp)
                            temp=[]
        return clauses
    def Request_5(self):#Tổng số cầu xây trên mỗi đảo phải bằng con số trên đảo đó
        clauses=[]
        count_clause=0
        count=0
        for i in range(self.range):
            for j in range(self.range):
                if (self.grid[i][j]!=0):
                    temp=[]
                    count=0
                    for c in range(4):
                        ni,nj=self.Neightbour(i,j,c)
                        if (ni==-1 or nj==-1):continue
                        else:
                            #Liệt kê các cầu của đảo
                            temp.append(self.To_index(i,j,ni,nj,0))
                            temp.append(self.To_index(i,j,ni,nj,1))
                            count+=2
                    #Kiểm tra tổng số cầu có bằng số trên đảo không
                    if (count>=self.grid[i][j]):
                        clause_tg=[]
                        for c in range(self.limit_range[count][self.grid[i][j]]):
                            temp_limit=self.limit[(count,self.grid[i][j],c)]  
                            temp_res= [x * y*-1 for x, y in zip(temp, temp_limit)]   
                            for l in range(len(temp_res)):
                                add_temp=[]
                                add_temp.append(-1*self.min_index)
                                add_temp.append(-1*temp_res[l])
                                clauses.append(add_temp)
                            temp_res.append(self.min_index)
                            clauses.append(temp_res)
                            
                            clause_tg.append(self.min_index)
                            self.min_index+=1
                        clauses.append(clause_tg)
                    else:
                        temp.append(-1)
                        clauses.append(temp)
                        temp.append(1)
                        clauses.append(temp)
        return clauses



    def Request_6(self):#Các đảo liên kết với nhau (có thể đi đến với đảo đầu tiên) 
        self.count=0
        final_clauses=[]
        def uf_find(parent, i):
            """Tìm gốc của đỉnh i trong cấu trúc union–find."""
            if parent[i] != i:
                parent[i] = uf_find(parent, parent[i])
            return parent[i]

        def uf_union(parent, rank, i, j):
            """Hợp nhất hai tập hợp chứa i và j. Trả về True nếu hợp nhất thành công (không tạo chu trình)."""
            root_i = uf_find(parent, i)
            root_j = uf_find(parent, j)
            if root_i == root_j:
                return False  # Thêm cạnh này sẽ tạo chu trình
            if rank[root_i] < rank[root_j]:
                parent[root_i] = root_j
            elif rank[root_i] > rank[root_j]:
                parent[root_j] = root_i
            else:
                parent[root_j] = root_i
                rank[root_i] += 1
            return True

        def backtrack(start, current_tree, parent, rank):
            if len(current_tree) == self.islands_count - 1:
                self.count=self.count+1
                final_clauses.append(current_tree.copy())
                return
            for i in range(start, self.num_edge):
                u, v, edge_id = self.edges[i]
                # Nếu chưa chọn cạnh nào, chỉ cho chọn các cạnh mà có đảo 0
                if not current_tree and 0 not in (u, v):
                    continue
                # Kiểm tra xem thêm cạnh (u,v) có tạo chu trình không
                if uf_find(parent, u) != uf_find(parent, v):
                    # Tạo bản sao của cấu trúc union-find cho nhánh hiện tại
                    new_parent = parent.copy()
                    new_rank = rank.copy()
                    uf_union(new_parent, new_rank, u, v)
                    current_tree.append(-1*edge_id)
                    backtrack(i + 1, current_tree, new_parent, new_rank)
                    current_tree.pop()
        
        parent = [i for i in range(self.islands_count)]
        rank = [0] * self.islands_count
        backtrack(0, [], parent, rank)


        temp=[]
        ano_clause=[]
        add_clause=[]
        for clause in final_clauses:
            for ele in clause:
                temp=[-1*ele,-1*self.min_index]
                add_clause.append(temp)
            temp=[]
            clause.append(self.min_index)
            ano_clause.append(self.min_index)
            self.min_index+=1
        final_clauses.append(ano_clause)
        final_clauses.extend(add_clause)
        return final_clauses
                
                   
    
    def Solve(self):
        # Lấy tất cả các mệnh đề CNF
        cnf_clauses=[]
        cnf_clauses_2 = self.Request_2()
        
        cnf_clauses_5=self.Request_5()
        cnf_clauses=cnf_clauses_5
        if (cnf_clauses_2!=[]):
            cnf_clauses+=cnf_clauses_2
        cnf_clauses_4=self.Request_4()
        if (cnf_clauses_4!=[]):
            cnf_clauses+=cnf_clauses_4
        for i in range(self.range):
            for j in range(self.range):
                if self.grid[i][j]!=0:
                    for c in range(2,4):
                        ni,nj=self.Neightbour(i,j,c)
                        if (ni==-1 or nj==-1):continue
                        temp=[]
                        temp.append([self.To_index(i,j,ni,nj,0)])
                        temp_clauses=cnf_clauses+temp
                        with Solver(name="g3") as solver:
                            solver.append_formula(temp_clauses)
                            if solver.solve():
                                self.edges[self.num_edge]=(self.is_numth[(i,j)],self.is_numth[(ni,nj)],self.To_index(i,j,ni,nj,0))
                                self.num_edge+=1
        cnf_clauses_6=self.Request_6()
        if (cnf_clauses_6!=[]):
            cnf_clauses+=cnf_clauses_6
        print('finishcnf')
        print(cnf_clauses)
        print(len(cnf_clauses))
        answer=[]
        solution = astar_CNF(cnf_clauses, {},get_variables(cnf_clauses))
        for num in solution:
            if (num>0 and num<4*self.islands_count+1):
                answer.append(num)
        print(answer)
        answer.sort()
        self.Output(answer)

        return
        print("số biến:", self.min_index)
        print("số mệnh đề:",len(cnf_clauses))
        # Dùng bộ giải SAT
        with Solver(name="g3") as solver:
            solver.append_formula(cnf_clauses)
            if solver.solve():
                solution = solver.get_model()
                answer=[]
                for num in solution:
                    if (num>0 and num<4*self.islands_count+1):
                        answer.append(num)
                answer.sort()
                self.Output(answer)
            else:
                print("XXX hết lời giải hợp lệ.")
    
    def re_index(self,num):
        num-=1
        o=num%2
        num=num//2
        direct=num%2
        num=num//2
        x1,y1=self.posxy[num]
        x2,y2=self.Neightbour(x1,y1,direct+2)
        return x1,y1,x2,y2,o
    
    def Output(self,solution):
        resgrid = [['0'] * self.range for _ in range(self.range)]
        for i in range(self.range):
            for j in range(self.range):
                if (self.grid[i][j]!=0):
                    resgrid[i][j]=str(self.grid[i][j])
        for num in solution:
            x1,y1,x2,y2,o=self.re_index(num)
            if (x1==x2):
                if (o==0):
                    char='-'
                else:char='='
                for j in range(y1+1,y2): resgrid[x1][j]=char
            else:
                if (o==0):
                    char='|'
                else:
                    char='$'
                for i in range(x1+1,x2): resgrid[i][y1]=char
        for i in range(self.range):
            print(resgrid[i])

def main():
    islands=Hashiwokakero_Grids()
    islands.Solve()


if __name__=="__main__":
    main()