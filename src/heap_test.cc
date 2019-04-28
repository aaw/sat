#include "flags.h"
#include "logging.h"
#include "heap.h"

#define EXPECT_EQ(x,y) if ((x) != (y)) { LOG(0) << #x << " != " << #y; }
#define TEST(x,y) static void test_##x() \
    { LOG(1) << "--------- Running " << __func__ << " ---------" ; y \
      LOG(2) << "--------- Finished " << __func__ << " ---------"; }
#define RUNTEST(x) test_##x()

TEST(basic,
     Heap<2> h(1);
     EXPECT_EQ(h.delete_max(), 1);
     EXPECT_EQ(h.delete_max(), lit_nil);
     EXPECT_EQ(h.delete_max(), lit_nil);
    )

TEST(double_insert,
     Heap<2> h(1);
     h.insert(1);
     h.insert(1);
     EXPECT_EQ(h.delete_max(), 1);
     EXPECT_EQ(h.delete_max(), lit_nil);
    )

TEST(insert_after_delete,
     Heap<2> h(1);
     LOG(0) << h.debug();
     EXPECT_EQ(h.delete_max(), 1);
     EXPECT_EQ(h.delete_max(), lit_nil);
     LOG(0) << h.debug();
     h.insert(1);
     LOG(0) << h.debug();
     EXPECT_EQ(h.delete_max(), 1);
     EXPECT_EQ(h.delete_max(), lit_nil);
     h.insert(2);
     EXPECT_EQ(h.delete_max(), 2);
     EXPECT_EQ(h.delete_max(), lit_nil);     
    )

int main(int argc, char **argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx)) <<
        "Usage: " << argv[0] << " <filename>";

    LOG(0) << "Running all tests. No output below means everything passes.";
    RUNTEST(basic);
    RUNTEST(double_insert);
    RUNTEST(insert_after_delete);
}
