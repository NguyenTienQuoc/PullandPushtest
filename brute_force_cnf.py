from helper_function import all_true_clauses, assignment_to_model, fill_value_to_unit_clauses, select_most_frequent_variable
def brute_force(clauses, assignment, variables):
    # Nếu đã gán đủ các biến, kiểm tra xem toàn bộ các mệnh đề có thỏa không.
    if len(assignment) == len(variables):
        if all_true_clauses(clauses, assignment):
            return assignment_to_model(assignment)
        else:
            return None

    next_var=select_most_frequent_variable(clauses,assignment,variables)

    # Thử gán cả True và False cho biến được chọn.
    for value in [True, False]:
        new_assignment = assignment.copy()
        new_assignment[next_var] = value
        # Áp dụng unit propagation để lan tỏa các gán bắt buộc (nếu có)
        new_assignment = fill_value_to_unit_clauses(clauses, new_assignment)
        result = brute_force(clauses, new_assignment, variables)
        if result is not None:
            return result

    return None