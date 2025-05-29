from helper_function import all_true_clauses, assignment_to_model, fill_value_to_unit_clauses, select_most_frequent_variable, contain_false_clause
def back_track(clauses,assignment,variables):
    if(len(assignment)==len(variables)):
        if all_true_clauses(clauses,assignment):
            return assignment_to_model(assignment)
        else:
            return None
    # Quay lui khi gặp điều kiện sai
    if contain_false_clause(clauses,assignment):
        return None
    
    new_variable=select_most_frequent_variable(clauses,assignment,variables)

    for value in[True, False]:
        # Gán giá trị mới cho biến được chọn
        new_assignment=assignment.copy()
        new_assignment[new_variable]=value
        # Điền giá trị cho các mệnh đề đơn vị
        new_assignment=fill_value_to_unit_clauses(clauses,new_assignment)
        result=back_track(clauses,new_assignment,variables)
        if result is not None:
            return result
    return None