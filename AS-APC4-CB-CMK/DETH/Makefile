EXE = connect-4
EXE_RANDOM_AI = ai_random.so
EXE_KID_AI = ai_kid.so
EXE_PRO_AI = ai_pro.so
SOURCES = main.c common.c
SOURCES_RANDOM_AI = ai_random.cpp common.c
SOURCES_KID_AI = ai_kid.cpp common.c
SOURCES_PRO_AI = ai_pro.cpp common.c
OBJS = $(addsuffix .o, $(basename $(notdir $(SOURCES))))
OBJS_RANDOM_AI = $(addsuffix .o, $(basename $(notdir $(SOURCES_RANDOM_AI))))
OBJS_KID_AI = $(addsuffix .o, $(basename $(notdir $(SOURCES_KID_AI))))
OBJS_PRO_AI = $(addsuffix .o, $(basename $(notdir $(SOURCES_PRO_AI))))
UNAME_S := $(shell uname -s)

CFLAGS += -O3 -march=native -Wall -Wformat -Wextra -Wno-unused-result -Wno-unused-parameter -Wno-unused-const-variable -fPIC
CXXFLAGS += ${CFLAGS} -std=c++2a
LIBS = -ldl
LIBS_RANDOM_AI =
LIBS_KID_AI =
LIBS_PRO_AI =

all: $(EXE) $(EXE_RANDOM_AI) $(EXE_KID_AI) $(EXE_PRO_AI)
	@echo Build complete

$(EXE): $(OBJS)
	$(CC) -o $@ $^ $(LIBS)

$(EXE_RANDOM_AI): $(OBJS_RANDOM_AI)
	$(CXX) -shared -o $@ $^ $(LIBS_RANDOM_AI)

$(EXE_KID_AI): $(OBJS_KID_AI)
	$(CXX) -shared -o $@ $^ $(LIBS_KID_AI)

$(EXE_PRO_AI): $(OBJS_PRO_AI)
	$(CXX) -shared -o $@ $^ $(LIBS_PRO_AI)

clean:
	rm -f $(EXE) $(OBJS)
	rm -f $(EXE_RANDOM_AI) $(OBJS_RANDOM_AI)
	rm -f $(EXE_KID_AI) $(OBJS_KID_AI)
	rm -f $(EXE_PRO_AI) $(OBJS_PRO_AI)

re:
	$(MAKE) clean
	$(MAKE) all