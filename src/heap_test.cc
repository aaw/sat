#include "flags.h"
#include "logging.h"
#include "heap.h"

#define EXPECT_EQ(x,y) if ((x) != (y)) { LOG(0) << #x << " != " << #y; }
#define TEST(x,y) static void test_##x() \
    { LOG(1) << "--------- Running " << __func__ << " ---------" ; y \
      LOG(3) << "--------- Finished " << __func__ << " ---------"; }
#define RUN(x) test_##x()

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
     EXPECT_EQ(h.delete_max(), 1);
     EXPECT_EQ(h.delete_max(), lit_nil);
     h.insert(1);
     EXPECT_EQ(h.delete_max(), 1);
     EXPECT_EQ(h.delete_max(), lit_nil);
    )

TEST(delete_max,
     Heap<2> h(2);
     h.bump(2);
     EXPECT_EQ(h.delete_max(), 2);
     EXPECT_EQ(h.delete_max(), 1);
     EXPECT_EQ(h.delete_max(), lit_nil);
     h.insert(2);
     EXPECT_EQ(h.delete_max(), 2);
     h.insert(1);
     EXPECT_EQ(h.delete_max(), 1);
     h.insert(1);
     h.insert(2);
     EXPECT_EQ(h.delete_max(), 2);
     EXPECT_EQ(h.delete_max(), 1);
     EXPECT_EQ(h.delete_max(), lit_nil);
    )

TEST(multiple_bumps_2,
     Heap<2> h(10);
     for (int i = 0; i < 200; ++i) { h.bump(10); }
     for (int i = 0; i < 50; ++i) { h.bump(8); }
     for (int i = 0; i < 180; ++i) { h.bump(9); }
     for (int i = 0; i < 30; ++i) { h.bump(6); }
     for (int i = 0; i < 100; ++i) { h.bump(8); h.bump(7); }
     // 10 has been bumped 200 times,
     // 9 has been bumped 180 times,
     // 8 has been bumped 150 times,
     // 7 has been bumped 100 times,
     // 6 has been bumped 30 times.
     EXPECT_EQ(h.delete_max(), 10);
     EXPECT_EQ(h.delete_max(), 9);
     EXPECT_EQ(h.delete_max(), 8);
     EXPECT_EQ(h.delete_max(), 7);
     EXPECT_EQ(h.delete_max(), 6);
    )

TEST(multiple_bumps_3,
     Heap<3> h(10);
     for (int i = 0; i < 200; ++i) { h.bump(10); }
     for (int i = 0; i < 50; ++i) { h.bump(8); }
     for (int i = 0; i < 180; ++i) { h.bump(9); }
     for (int i = 0; i < 30; ++i) { h.bump(6); }
     for (int i = 0; i < 100; ++i) { h.bump(8); h.bump(7); }
     // 10 has been bumped 200 times,
     // 9 has been bumped 180 times,
     // 8 has been bumped 150 times,
     // 7 has been bumped 100 times,
     // 6 has been bumped 30 times.
     EXPECT_EQ(h.delete_max(), 10);
     EXPECT_EQ(h.delete_max(), 9);
     EXPECT_EQ(h.delete_max(), 8);
     EXPECT_EQ(h.delete_max(), 7);
     EXPECT_EQ(h.delete_max(), 6);
    )

TEST(multiple_bumps_4,
     Heap<4> h(10);
     for (int i = 0; i < 200; ++i) { h.bump(10); }
     for (int i = 0; i < 50; ++i) { h.bump(8); }
     for (int i = 0; i < 180; ++i) { h.bump(9); }
     for (int i = 0; i < 30; ++i) { h.bump(6); }
     for (int i = 0; i < 100; ++i) { h.bump(8); h.bump(7); }
     // 10 has been bumped 200 times,
     // 9 has been bumped 180 times,
     // 8 has been bumped 150 times,
     // 7 has been bumped 100 times,
     // 6 has been bumped 30 times.
     EXPECT_EQ(h.delete_max(), 10);
     EXPECT_EQ(h.delete_max(), 9);
     EXPECT_EQ(h.delete_max(), 8);
     EXPECT_EQ(h.delete_max(), 7);
     EXPECT_EQ(h.delete_max(), 6);
    )
     
int main(int argc, char **argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx)) <<
        "Usage: " << argv[0] << " <filename>";

    LOG(0) << "Running all tests. No output below means everything passes.";
    RUN(basic);
    RUN(double_insert);
    RUN(insert_after_delete);
    RUN(delete_max);
    RUN(multiple_bumps_2);
    RUN(multiple_bumps_3);
    RUN(multiple_bumps_4);
}
