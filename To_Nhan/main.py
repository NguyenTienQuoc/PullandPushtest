from pysat.solvers import Solver
from pysat.card import *
from itertools import product
from astar_cnf import astar_CNF
from backtrack_cnf import back_track
from brute_force_cnf import brute_force
from helper_function import get_variables
import time
import os

Moves=[[-1,0],[0,-1],[1,0],[0,1]]
      
class Hashiwokakero_Grids:
    def __init__(self,inputh):
        self.level=inputh
        self.total=0
        self.islands_count=0
        self.is_numth={}
        filename="./Inputs/input-"
        if (inputh!=10): filename+='0'
        filename+=str(inputh)+".txt"
        with open(filename,'r',encoding='utf-8') as file:
            line=file.readline()
            parts=line.split(', ')
            self.range=len(parts)
            self.grid = [[0] * self.range for _ in range(self.range)]
            for j in range(len(parts)):
                self.grid[0][j]=int(parts[j])
                if (self.grid[0][j]!=0):
                    self.is_numth[(0,j)]=self.islands_count
                    self.islands_count+=1
            for i in range(1,self.range):
                line=file.readline()
                parts=line.split(', ')
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
        self.edges=[]
        self.limit_range=[[0]*9 for _ in range(9)]
        self.limit = {}
        self.variables={}
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
    
    def re_index(self,num):
        num-=1
        o=num%2
        num=num//2
        direct=num%2
        num=num//2
        x1,y1=self.posxy[num]
        x2,y2=self.Neightbour(x1,y1,direct+2)
        return x1,y1,x2,y2,o

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
                            self.variables[(self.min_index)]=[x * y for x, y in zip(temp, temp_limit)] 
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

    def convert_to_pysat(self,nested_list):
        if not nested_list:
            return []
        
         #Sử dụng tích Descartes để phân phối OR vào AND
        cnf_clauses = [list(clause) for clause in product(*nested_list)]
        return cnf_clauses
    def filter_subsets(self,clauses):
        # Kết quả sẽ lưu các clause không phải là tập con của clause nào khác
        filtered = []
        for clause in clauses:
            filtered.append(clause)
            break
        for i in range(1,len(clauses)):
            test=clauses[i]
            check=False
            for j in range(len(filtered)):
                result=filtered[j]
                if set(result) >= set(test):
                    check=True
                    break
                elif set(test) > set(result):
                    filtered[j]=test
                    check=True
                    break
            if check==False:
                filtered.append(test)
        return filtered
    
    def Request_6_part1(self):
        temp=[]
        toconvert=[]
        clauses=[]
        for num1 in range(self.islands_count):
            x0,y0=self.posxy[num1]
            toconvert=[]
            converted=[]
            for c in range(4):
                x1,y1=self.Neightbour(x0,y0,c)
                if (x1==-1 or y1==-1): continue
                else:
                    temp=[]
                    temp.append(-1*self.To_index(x0,y0,x1,y1,0))
                    temp.append(-1*(self.min_index+self.is_numth[(x1,y1)]))
                    temp.append(self.min_index+num1)
                    clauses.append(temp)
                    temp=[]
                    temp.append(self.To_index(x0,y0,x1,y1,0))
                    temp.append(self.min_index+self.is_numth[(x1,y1)])
                    toconvert.append(temp)
            if (toconvert!=[]):
                converted=self.convert_to_pysat(toconvert)
                for clause in converted:
                    clause.append(-1*(self.min_index+num1))
                    clauses.append(clause)
        temp=[]
        temp.append(self.min_index)
        clauses.append(temp)
        self.total=self.min_index+self.islands_count
        return clauses


    def Request_6_part2(self,clauses):#Các đảo liên kết với nhau (có thể đi đến với đảo đầu tiên) 
        final_temp_clauses=[]
        need_work=False
        with Solver(name="g3") as solver:
                solver.append_formula(clauses)
                if solver.solve():
                    solution = solver.get_model()
                    for num in solution:
                        if (num>=self.min_index or num<=-self.min_index):
                            if (num<0):
                                need_work=True
        if (need_work==False):
            return []
        def backtrack(clauses,temp_clauses):
            # Dùng bộ giải SAT
            with Solver(name="g3") as solver:
                solver.append_formula(clauses+temp_clauses)
                if solver.solve():
                    solution = solver.get_model()
                    check=[]
                    check_nega=False
                    for num in solution:
                        if (num>=self.min_index or num<=-self.min_index):
                            check.append(num)
                            if (num<0):
                                check_nega=True
                    if (check_nega==False):
                        if temp_clauses==[]:
                            return
                        if temp_clauses==[[]]:
                            return 
                        result=[]
                        for x in temp_clauses:
                            result.append(-1*x[0])
                        result.sort()
                        final_temp_clauses.append(result)
                        return
                    for i in range(len(check)):
                        if check[i]<0:
                            #print(i,':',temp_clauses)
                            x0,y0=self.posxy[check[i]*-1-self.min_index]
                            for c in range(4):
                                x1,y1=self.Neightbour(x0,y0,c)
                                if ((x1==-1 or y1==-1 or self.To_index(x0,y0,x1,y1,0) not in self.edges) or check[self.is_numth[(x1,y1)]]<0): continue
                                else:
                                    ntemp=[]
                                    ntemp.append(self.To_index(x0,y0,x1,y1,0))
                                    if (ntemp not in clauses and(ntemp not in temp_clauses)):
                                        new_temp_clauses=temp_clauses.copy()
                                        new_temp_clauses.append(ntemp)
                                        if (final_temp_clauses!=[]):
                                            return
                                        backtrack(clauses, new_temp_clauses)
        
        
        try_temp=[]
        backtrack(clauses, try_temp)
        final_temp_clauses=self.filter_subsets(final_temp_clauses)
        temp=[]
        ano_clause=[]
        add_clause=[]
        for clause in final_temp_clauses:
            for ele in clause:
                temp=[-1*ele,-1*self.total]
                add_clause.append(temp)
            temp=[]
            clause.append(self.total)
            ano_clause.append(self.total)
            self.total+=1
        final_temp_clauses.append(ano_clause)
        final_temp_clauses.extend(add_clause)
        if final_temp_clauses==[[]]:
            return [[-1],[1]]
        return final_temp_clauses
                
                   
    
    def Solve(self,choice):
        # Lấy tất cả các mệnh đề CNF
        cnf_clauses=[]
        cnf_clauses_2 = self.Request_2()     
        cnf_clauses_5=self.Request_5()
        cnf_clauses=cnf_clauses_5
        if (cnf_clauses_2!=[]):
            cnf_clauses+=cnf_clauses_2
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
                                self.edges.append(self.To_index(i,j,ni,nj,0))
        cnf_clauses_6_1=self.Request_6_part1()
        if (cnf_clauses_6_1!=[]):
            cnf_clauses+=cnf_clauses_6_1
        cnf_clauses_6_2=self.Request_6_part2(cnf_clauses)
        if (cnf_clauses_6_2!=[] and cnf_clauses_6_2!=[[]]):
            cnf_clauses+=cnf_clauses_6_2
        print(cnf_clauses)
        with Solver(name="g3") as solver:
            solver.append_formula(cnf_clauses)
            if solver.solve(): choice=choice
            else:
                print("XXX không có lời giải hợp lệ.")
                return
        if (choice==1):
            start = time.perf_counter()
            # Dùng bộ giải SAT
            with Solver(name="g3") as solver:
                solver.append_formula(cnf_clauses)
                if solver.solve():
                    solution = solver.get_model()
                    end = time.perf_counter()
                    time_count = end-start
                    answer=[]
                    for num in solution:
                        if (num>0 and num<4*self.islands_count+1):
                            answer.append(num)
                    answer.sort()
                    print("Nghiệm tìm được của pySAT:")
                    print(answer)
                    print(f"Thời gian chạy pySAT: {time_count:.6f} giây\n")
                    self.Output(answer)
        elif (choice==2):
            start = time.perf_counter()
            solution = astar_CNF(cnf_clauses, {},get_variables(cnf_clauses))
            end = time.perf_counter()
            time_count = end-start
            answer=[]
            for num in solution:
                if (num>0 and num<4*self.islands_count+1):
                    answer.append(num)
            answer.sort()
            print("Nghiệm tìm được của A*:")
            print(answer)
            print(f"Thời gian chạy A*: {time_count:.6f} giây\n")
            self.Output(answer)
        elif (choice==3):
            start = time.perf_counter()
            solution = brute_force(cnf_clauses, {},get_variables(cnf_clauses))
            end = time.perf_counter()
            time_count = end-start
            answer=[]
            for num in solution:
                if (num>0 and num<4*self.islands_count+1):
                    answer.append(num)
            answer.sort()
            print("Nghiệm tìm được của Brute force:")
            print(answer)
            print(f"Thời gian chạy Brute force: {time_count:.6f} giây\n")
            self.Output(answer)
        elif (choice==4):
            start = time.perf_counter()
            solution = back_track(cnf_clauses, {},get_variables(cnf_clauses))
            end = time.perf_counter()
            time_count = end-start
            answer=[]
            for num in solution:
                if (num>0 and num<4*self.islands_count+1):
                    answer.append(num)
            answer.sort()
            print("Nghiệm tìm được của Back tracking:")
            print(answer)
            print(f"Thời gian chạy Back tracking: {time_count:.6f} giây\n")
            self.Output(answer)
        elif (choice==5):
            start = time.perf_counter()
            # Dùng bộ giải SAT
            with Solver(name="g3") as solver:
                solver.append_formula(cnf_clauses)
                if solver.solve():
                    solution = solver.get_model()
                    end = time.perf_counter()
                    time_count = end-start
                    answer=[]
                    for num in solution:
                        if (num>0 and num<4*self.islands_count+1):
                            answer.append(num)
                    answer.sort()
                    print("Nghiệm tìm được của pySAT: ",end='')
                    print(answer)
                    print(f"Thời gian chạy pySAT: {time_count:.6f} giây\n")
            #Dùng A*
            start = time.perf_counter()
            solution = astar_CNF(cnf_clauses, {},get_variables(cnf_clauses))
            end = time.perf_counter()
            time_count = end-start
            answer=[]
            for num in solution:
                if (num>0 and num<4*self.islands_count+1):
                    answer.append(num)
            answer.sort()
            print("Nghiệm tìm được của A*: ",end='')
            print(answer)
            print(f"Thời gian chạy A*: {time_count:.6f} giây\n")
            #Dùng brute force
            start = time.perf_counter()
            solution = brute_force(cnf_clauses, {},get_variables(cnf_clauses))
            end = time.perf_counter()
            time_count = end-start
            answer=[]
            for num in solution:
                if (num>0 and num<4*self.islands_count+1):
                    answer.append(num)
            answer.sort()
            print("Nghiệm tìm được của Brute force: ",end='')
            print(answer)
            print(f"Thời gian chạy Brute force: {time_count:.6f} giây\n")
            #Dùng back tracking
            start = time.perf_counter()
            solution = back_track(cnf_clauses, {},get_variables(cnf_clauses))
            end = time.perf_counter()
            time_count = end-start
            answer=[]
            for num in solution:
                if (num>0 and num<4*self.islands_count+1):
                    answer.append(num)
            answer.sort()
            print("Nghiệm tìm được của Back tracking: ",end='')
            print(answer)
            print(f"Thời gian chạy Back tracking: {time_count:.6f} giây\n")
        
        return
        
    
    def Output(self,solution):
        inputh=self.level
        dirPath = "./Outputs"
        if not os.path.exists(dirPath):
            os.makedirs(dirPath)
        filename = dirPath + "/output-"
        if (inputh!=10): filename+='0'
        filename+=str(inputh)+".txt"
        with open(filename, 'w') as f:
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
                f.write('[')
                for j in range(self.range):
                    resgrid[i][j]=' "'+resgrid[i][j]+'" '
                    f.write(resgrid[i][j])
                    if (j!=self.range-1):
                        f.write(',')
                f.write(']\n')
def Menu():
    print("1. Giải bằng phương pháp Pysat")
    print("2. Giải bằng phương pháp A*")
    print("3. Giải bằng phương pháp brute force")
    print("4. Giải bằng phương pháp backtrack")
    print("5. So sánh các phương pháp")
    print("6. Thoát")
    choice = int(input("Nhập lựa chọn của bạn: "))
    if choice == 6:
        exit()
    elif choice>6 or choice<1:
        print("Lựa chọn không hợp lệ. Nhập lại.")
        Menu()
    print("Chọn một trong 10 input bằng cách nhập số từ 1 đến 10:")
    inputh=int(input("Lựa chọn input: "))
    if inputh>10 or inputh<1:
        print("Lựa chọn không hợp lệ. Nhập lại.")
        Menu()
    return choice,inputh
choice,inputh=Menu()

islands=Hashiwokakero_Grids(inputh)
islands.Solve(choice)
