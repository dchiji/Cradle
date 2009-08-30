-module(dssg).
-export([atom_hash/2, bn_pow/2]).
-export([start/0, start/1, dssg_pid/0, getv/1, putv/2]).
 
%-define(debug(X), (begin io:format("*** DEBUG ~p ~p   ~p~n", [?MODULE, ?LINE, X]) end)).
-define(debug(X), pass).
 
 
% Utilities
 
bn_pow(N, M) ->   % bn ; big-num
   if
      M == 0 -> N;
      true   -> N * bn_pow(2, M - 1)
   end.
 
swell_list(List) ->
   if
      length(List) > 20 -> List;
      true              -> swell_list(List ++ List)
   end.
 
atom_hash(List, Max) ->
   (lists:foldl((fun(X, Sum) -> X * Sum end), 1, swell_list(List))) rem Max.
 
next([[NextHash, NextPid] | _], Hash) when NextHash == Hash  -> [NextHash, NextPid];
next([[NextHash, NextPid]], _Hash)                           -> [NextHash, NextPid];
next([[NextHash, NextPid], [NextHash2, NextPid2] | T], Hash) ->
   if
      NextPid == NextPid2 ->
         [NextHash, NextPid];
      NextHash < Hash andalso Hash < NextHash2 ->
         [NextHash, NextPid];
      NextHash < Hash andalso NextHash2 < Hash andalso NextHash2 < NextHash ->
         [NextHash, NextPid];
      NextHash > Hash andalso NextHash2 > Hash andalso NextHash2 < NextHash ->
         [NextHash, NextPid];
      true ->
         next([[NextHash2, NextPid2] | T], Hash)
   end.
 
allot(MyHash, NewHash, NextHash, Table) ->
   allot(MyHash, NewHash, NextHash, ets:tab2list(Table), [], []).
 
allot(_, _, _, [], List0, List1) ->
   {List0, List1};
 
allot(MyHash, _, MyHash, List, _, _) ->
   {List, List};
 
allot(MyHash, NewHash, NextHash, [{Key, {Hash, Value}} | T], List0, List1) ->
   if
      NextHash < Hash ->
         allot(MyHash, NewHash, NextHash, T, List0, [{Key, {Hash, Value}} | List1]);
      Hash < NewHash ->
         allot(MyHash, NewHash, NextHash, T, [{Key, {Hash, Value}} | List0], List1);
      true ->
         allot(MyHash, NewHash, NextHash, T, [{Key, {Hash, Value}} | List0], [{Key, {Hash, Value}} | List1])
   end.
 
list2tab(List) ->
   list2tab(ets:new(undefined, [public, set]), List).
 
list2tab(Table, List) ->
   lists:foreach(fun(Tuple) -> ets:insert(Table, Tuple) end, List),
   Table.
 
 
% Sub Core
 
update(MyHash, MyWatched, [[Hash, Node, Watched] | T], N) ->
   update(MyHash, MyWatched, [[Hash, Node, Watched] | T], N, none).
 
update(MyHash, MyWatched, [[Hash, Node, Watched] | T], N, Option) ->
   update(MyHash, MyWatched, [[Hash, Node, Watched] | T], N, [], Option).
 
update(_, MyWatched, [[Hash, Node, MyWatched] | T], _, NewList, _) ->
   lists:reverse(lists:reverse([[Hash, Node, MyWatched] | T]) ++ NewList);
 
update(_, _, [none | T], _, NewList, _) ->
   lists:reverse(NewList) ++ [none | T];
 
update(_, _, [Next], _, NewList, _) ->
   lists:reverse([Next | NewList]);
 
update(MyHash, MyWatched, [[Hash, Node, Watched] | T], N, NewList, none) ->
   Watched ! {self(), {next, N}},
   receive
      {Watched, {ok, Next}} ->
         {T1, _} = lists:split(length(T) - 1, T),
         update(MyHash, MyWatched, [Next | T1], N, [[Hash, Node, Watched] | NewList], none)
   after
      500 ->
         [{1, [[NextHash, _, _] | _]}] = ets:lookup(nodetable, 1),
         {_KeyValue0, KeyValue1} = allot(MyHash, Hash, NextHash, keyvalue),
 
         {[NewHash, NewPid, NewWatched], T1, NewList1} = case NewList of
            [] ->
               [New | T0] = T,
               {New, T0, NewList};
            _ ->
               [New | NewList0] = NewList,
               {New, T, NewList0}
         end,
         NewWatched ! {self(), {repair, MyHash, 1, KeyValue1}},
         receive
            {response_repair, KeyValueList} ->
               list2tab(keyvalue, KeyValueList)
         end,
         update(MyHash, MyWatched, [[NewHash, NewPid, NewWatched] | [new | [T1]]], N, NewList1, none)
   end;
 
update(MyHash, MyWatched, [[Hash, Node, Watched] | T], N, NewList, noreplicate) ->
   Watched ! {self(), {next, N}},
   receive
      {Watched, {ok, Next}} ->
         {T1, _} = lists:split(length(T) - 1, T),
         update(MyHash, MyWatched, [Next | T1], N, [[Hash, Node, Watched] | NewList], noreplicate)
   after
      500 ->
         {[NewHash, NewPid, NewWatched], T1, NewList1} = case NewList of
            [] ->
               [New | T0] = T,
               {New, T0, NewList};
            _ ->
               [New | NewList0] = NewList,
               {New, T, NewList0}
         end,
         update(MyHash, MyWatched, [[NewHash, NewPid, NewWatched] | [new | [T1]]], N, NewList1, noreplicate)
   end.
 
watch(MyHash, MyWatched, N) ->
   watch(MyHash, MyWatched, N, none, infinity).
 
watch(MyHash, MyWatched, N, Option) ->
   watch(MyHash, MyWatched, N, Option, infinity).
 
watch(MyHash, MyWatched, N, Option, Time) ->
   receive
      {join, [Hash, Node, Watched]} ->
         [{N, Next}] = ets:lookup(nodetable, N),
         {T, _} = lists:split(length(Next) - 1, Next),
         List1 = update(MyHash, MyWatched, [[Hash, Node, Watched] | T], N, Option),
         ets:insert(nodetable, {N, List1}),
         watch(MyHash, MyWatched, N, Option, 500)
   after
      Time ->
         [{N, List0}] = ets:lookup(nodetable, N),
         List1 = update(MyHash, MyWatched, List0, N, Option),
         ets:insert(nodetable, {N, List1}),
         watch(MyHash, MyWatched, N, Option, 500)
   end.
 
watched(MyHash, Table, KeyValue) ->
   receive
      {From, {next, N}} ->
         [{N, [Next | _]}] = ets:lookup(Table, N),
         From ! {self(), {ok, Next}},
         watched(MyHash, Table, KeyValue);
 
      {From, {repair, Hash, N, KeyValueList}} ->
         [{N, [[NextHash, _, _] | _]}] = ets:lookup(Table, N),
         {KeyValue0, _} = allot(Hash, MyHash, NextHash, KeyValue), 
         From ! {response_repair, KeyValue0},
 
         watched(MyHash, Table, list2tab(KeyValue, KeyValueList));
 
      {From, ping} ->
         From ! {self(), pong},
         watched(MyHash, Table, KeyValue);
 
      {_From, {replication, {Key, {Hash, Value}}}} ->
         ets:insert(KeyValue, {Key, {Hash, Value}}),
         watched(MyHash, Table, KeyValue)
   end.
 
skipnode() ->
   skipnode(1).
 
skipnode(N) ->
   case ets:lookup(nodetable, N) of
      []   -> [];
      [{N, List}] -> [List | skipnode(N + 1)]
   end.
 
setup_skiplist(MyHash, MyWatched, N) ->
   setup_skiplist(MyHash, MyWatched, 2, N).
 
setup_skiplist(_, _, N, N) ->
   ok;
 
setup_skiplist(MyHash, MyWatched, N, M) ->
   case find(MyHash + bn_pow(2, N), infinity) of
      {ok, Result} ->
         ets:insert(nodetable, {N, [Result, none]});
      {error, Status} ->
         ?debug({setup_skiplist, {status, Status}})
   end,
   ?debug({setup_skiplist, {n, N}, {m, M}}),
   spawn(fun() -> watch(MyHash, MyWatched, N, noreplicate) end),
   setup_skiplist(MyHash, MyWatched, N + 1, M).
 
 
% Core
 
loop(MyHash, MyWatched, MyWatch) ->
   ?debug(loop),
   receive
      {From, {find, Hash}} ->
         Nodes = [[NextHash, NextPid] || [[NextHash, NextPid, _] | _] <- skipnode()],
         [_Hash1, Pid] = next([[MyHash, self()] | Nodes], Hash),
         ?debug({find, {hash, Hash}, {from, From}, {pid, Pid}, {nodes, Nodes}}),
         if
            Pid == self() ->
               From ! {response_find, [MyHash, self(), MyWatched]};
            true ->
               Pid ! {From, {find, Hash}}
         end,
         loop(MyHash, MyWatched, MyWatch);
 
      %  main of join-proc
      {From, {join, Hash, Watched, Watch}} ->
         ?debug({join, {hash, Hash}}),
         Nodes = [[NextHash, NextPid] || [[NextHash, NextPid, _] | _] <- skipnode()],
         [_Hash1, Pid] = next([[MyHash, self()] | Nodes], Hash),
         if
            Pid == self() -> self() ! {From, {join_f, Hash, Watched, Watch}};
            true          -> Pid ! {From, {join, Hash, Watched, Watch}}
         end,
         loop(MyHash, MyWatched, MyWatch);
 
      %  final of join-proc
      {From, {join_f, MyHash, Watched, Watch}} ->
         From ! {response_join, {error, {conflict, {need, restart}}};

      {From, {join_f, Hash, Watched, Watch}} ->
         [{1, [[NextHash, NextPid, NextWatched] | _]}] = ets:lookup(nodetable, 1),
 
         {KeyValue0, KeyValue1} = allot(MyHash, Hash, NextHash, keyvalue),
         From ! {response_join, {ok, KeyValue1}},
 
         Watch ! {join, [NextHash, NextPid, NextWatched]},
         MyWatch ! {join, [Hash, From, Watched]},
 
         ets:delete(keyvalue),
         list2tab(ets:new(keyvalue, [public, set, named_table]), KeyValue0),
         loop(MyHash, MyWatched, MyWatch);
 
      %  get-proc
      {From, {get, Hash, Key}} ->
         ?debug({get, Hash, Key}),
         Nodes = [[NextHash, NextPid] || [[NextHash, NextPid, _] | _] <- skipnode()],
         [_Hash2, Pid] = next([[MyHash, self()] | Nodes], Hash),
         if
            Pid == self() ->
               case ets:lookup(keyvalue, Key) of
                  [] ->
                     From ! {response_get, Key, unknown};
                  [{Key, Value}] ->
                     From ! {response_get, Key, Value}
               end;
            true ->
               [[_, NextPid] | _] = Nodes,
               NextPid ! {From, {get, Hash, Key}}
         end,
         loop(MyHash, MyWatched, MyWatch);
 
      %  put-proc
      {_From, {put, Hash, Key, Value}} ->
         ?debug({put, {hash, Hash}, {key, Key}, {value, Value}}),
         Nodes = [[NextHash, NextPid] || [[NextHash, NextPid, _] | _] <- skipnode()],
         [_Hash2, Pid] = next([[MyHash, self()] | Nodes], Hash),
         if
            Pid == self() -> self() ! {_From, {put_f, Hash, Key, Value}};
            true          -> Pid ! {_From, {put, Hash, Key, Value}}
         end,
         loop(MyHash, MyWatched, MyWatch);
 
      %  final of join-proc
      {_From, {put_f, Hash, Key, Value}} ->
         ets:insert(keyvalue, {Key, {Hash, Value}}),
 
         [{1, [[_, _, Watched] | _]}] = ets:lookup(nodetable, 1),
         Watched ! {self(), {replication, {Key, {Hash, Value}}}},
         loop(MyHash, MyWatched, MyWatch)
   end.
 
 
% Interface
 
start() ->
   register(dssgsys, spawn(fun() -> start0(atom_to_list(node())) end)).
 
start(InitNode) ->
   register(dssgsys, spawn(fun() -> start0(atom_to_list(node()), InitNode) end)).
 
start0(Name, InitNode) ->
   MyHash = atom_hash(Name, bn_pow(2, 160)),
 
   ets:new(keyvalue, [public, set, named_table]),
   ets:new(nodetable, [public, set, named_table]),
   ets:insert(nodetable, {1, [none, none]}),
 
   Watched = spawn(fun() -> watched(MyHash, nodetable, keyvalue) end),
   Watch = spawn(fun() -> watch(MyHash, Watched, 1) end),
 
   case net_adm:ping(InitNode) of
      pong -> ok;
      pang -> exit(pang)
   end,
   Init = rpc:call(InitNode, dssg, dssg_pid, []),
   Init ! {self(), {join, MyHash, Watched, Watch}},
 
   receive
      {response_join, {ok, KeyValue}} ->
         ets:delete(keyvalue),
         list2tab(ets:new(keyvalue, [public, set, named_table]), KeyValue),
 
         spawn(fun() -> setup_skiplist(MyHash, Watched, 8) end),
 
         loop(MyHash, Watched, Watch);
      {response_join, {error, States}} ->
         {error, States};
      Any ->
         {nomatch, Any}
   end.
 
start0(Name) ->
   MyHash = atom_hash(Name, bn_pow(2, 160)),
 
   ets:new(keyvalue, [public, set, named_table]),
   ets:new(nodetable, [public, set, named_table]),
   ets:insert(nodetable, {1, [none, none]}),
 
   Watched = spawn(fun() -> watched(MyHash, nodetable, keyvalue) end),
   Watch = spawn(fun() -> watch(MyHash, Watched, 1) end),
   Watch ! {join, [MyHash, self(), Watched]},
 
   spawn(fun() -> setup_skiplist(MyHash, Watched, 8) end),
 
   loop(MyHash, Watched, Watch).
 
dssg_pid() ->
   whereis(dssgsys).
 
find(Hash) ->
   find(Hash, 1000).
 
find(Hash, Timeout) ->
   dssgsys ! {self(), {find, Hash}},
   receive
      {response_find, Reply} -> {ok, Reply}
   after
      Timeout -> {error, time_out}
   end.
 
getv(Key) ->
   getv(Key, 1000).
 
getv(Key, Timeout) ->
   dssgsys ! {self(), {get, atom_hash(atom_to_list(Key), bn_pow(2, 160)), Key}},
   receive
      {response_get, Key, Value} -> {ok, Value}
   after
      Timeout -> {error, time_out}
   end.
 
putv(Key, Value) ->
   dssgsys ! {self(), {put, atom_hash(atom_to_list(Key), bn_pow(2, 160)), Key, Value}}.
 
