FILE(GLOB files "*.c")
foreach(test_file IN LISTS files)
  get_filename_component(test ${test_file} NAME_WE)

  add_test(
    NAME ${test}
    COMMAND ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/cpp2c tr ${test_file})
endforeach()