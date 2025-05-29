# CÁC HÀM ĐƯỢC SỬ DỤNG TRONG THUẬT TOÁN A*, BRUTE FORCE VÀ BACKTRACKING
def is_True_clause(clause, assignment):
    """
    Mệnh đề là True nếu có ít nhất một biến trong mệnh đề là True .
    """
    return any((abs(lit) in assignment and assignment[abs(lit)] == (lit > 0)) for lit in clause)
def all_true_clauses(clauses, assignment):
    """
    Tất cả các mệnh đề đều là True nếu tất cả các mệnh đề đều là True với gán giá trị cho biến.
    """
    return all(is_True_clause(clause, assignment) for clause in clauses)
def contain_false_clause(clauses, assignment):
    """
    Kiểm tra xem có mệnh đề nào tất cả các biến đã gán giá trị nhưng giá trị mệnh đề False
    """
    for clause in clauses:
        all_assigned=True
        clause_val=False
        for literal in clause:
            if abs(literal) not in assignment:
                all_assigned=False
                break
            if (literal > 0) == assignment[abs(literal)]:
                clause_val=True
                break
        if all_assigned and not clause_val:
            return True
    return False

def assignment_to_model(assignment):
    """
    Chuyển đổi assignment (dict) thành model dạng danh sách literal (theo định dạng của PySAT).
    """
    model = []
    for var in sorted(assignment.keys()):
        if assignment[var]:
            model.append(var)
        else:
            model.append(-var)
    return model

def select_most_frequent_variable(clauses, assignment,variables):
    """
    Chọn biến xuất hiện nhiều nhất trong các mệnh đề chưa được gán giá trị.
    """
    frequency={}
    for clause in clauses:
        # Bỏ qua mệnh đề đã xác định giá trị
        if is_True_clause(clause, assignment):
            continue
        for literal in clause:
            if abs(literal) in assignment:
                continue
            frequency[abs(literal)] = frequency.get(abs(literal), 0) + 1
    if not frequency:
        for var in sorted(variables):
            if var not in assignment:
                return var
    return max(frequency,key=frequency.get)

def fill_value_to_unit_clauses(clauses, assignment):
    """
    Kiểm tra xem có mệnh đề nào chỉ cần gán giá trị 1 biến là trở thành True rồi gán
    """
    contain_unit_clause = True
    while contain_unit_clause:
        contain_unit_clause = False
        for clause in clauses:
            if is_True_clause(clause, assignment):
                continue
            # Tìm các biến chưa được gán trong mệnh đề
            unassigned = [literal for literal in clause if abs(literal) not in assignment]
            if len(unassigned) == 1:
                assignment[abs(unassigned[0])] = unassigned[0] > 0
                contain_unit_clause = True
                break
    return assignment

def get_variables(clauses):
    """
    Lấy ra danh sách các biến từ các mệnh đề trong CNF.
    """
    variables={abs(literal) for clause in clauses for literal in clause}
    return variables