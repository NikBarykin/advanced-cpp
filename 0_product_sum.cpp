#include <iostream>


bool rangeFind(size_t const* range_begin, size_t range_size, size_t target_value) {
  for (size_t i = 0; i < range_size; ++i) {
    if (range_begin[i] == target_value) {
      return true;
    }
  }
  return false;
}

long long computeSumImpl(size_t n_arrays, size_t const* array_sizes,
                         int const* const* arrays, size_t step_n,
                         size_t* used_indices) {
  if (step_n == n_arrays) {
    return 1;
  }

  long long result = 0;
  for (size_t i = 0; i < array_sizes[step_n]; ++i) {
    if (rangeFind(used_indices, step_n, i)) {
      continue;
    }
    used_indices[step_n] = i;
    result += arrays[step_n][i] * computeSumImpl(n_arrays, array_sizes, arrays,
                                                 step_n + 1, used_indices);
  }
  return result;
}

long long computeSum(size_t n_arrays, size_t const* array_sizes,
                     int const* const* arrays) {
  size_t* used_indices = new size_t[n_arrays];
  long long result =
      computeSumImpl(n_arrays, array_sizes, arrays, 0, used_indices);
  delete[] used_indices;
  return result;
}

int main(int argc, const char* argv[]) {
  size_t n_arrays = argc - 1;
  size_t* array_sizes = new size_t[n_arrays];
  int** arrays = new int*[n_arrays];
  for (size_t i = 0; i < n_arrays; ++i) {
    array_sizes[i] = atoi(argv[i + 1]);
    arrays[i] = new int[array_sizes[i]];
    for (size_t j = 0; j < array_sizes[i]; ++j) {
      std::cin >> arrays[i][j];
    }
  }

  std::cout << computeSum(n_arrays, array_sizes, arrays) << std::endl;

  delete[] array_sizes;
  for (size_t i = 0; i < n_arrays; ++i) {
    delete[] arrays[i];
  }
  delete[] arrays;
  return 0;
}
