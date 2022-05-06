CC ?= gcc

CFLAGS := -Wall -Wextra -Wno-unused-parameter -g -O2 

DEFINES := -DHAVE_CONFIG_H 

LDFLAGS := -lpthread

C_SRCS :=   protocol.c \
          api.c \
          version.c \
          ip_acl.c \
          main.c \
          commandline.c \
          conf.c \
          debug.c \
          fw_iptables.c \
          firewall.c \
          gateway.c \
          centralserver.c \
          http.c \
          auth.c \
          client_list.c \
          util.c \
          wdctl_thread.c \
          ping_thread.c \
          safe.c \
          httpd_thread.c \
          simple_http.c \
          pstring.c \
          wd_util.c \
#          wdctl.c 

OBJECTS := $(patsubst %.c,%.o,$(C_SRCS))

%.o: %.c
	$(CC) $(DEFINES) $(CFLAGS) -c $< -o $@ 

auth_server: $(OBJECTS)
	$(CC) -o $@ $^ $(LDFLAGS)

clean:
	rm auth_server *.o

