import 'package:flutter/material.dart';
import 'package:flutter/services.dart';

import 'package:go_router/go_router.dart';

class ScaffoldWithNavBarTabItem extends BottomNavigationBarItem {
  const ScaffoldWithNavBarTabItem(
      {required this.initialLocation, required Widget icon, String? label})
      : super(icon: icon, label: label);

  /// The initial location/path
  final String initialLocation;
}

class ScaffoldWithBottomNavBar extends StatefulWidget {
  const ScaffoldWithBottomNavBar({Key? key, required this.child}) : super(key: key);
  final Widget child;

  @override
  State<ScaffoldWithBottomNavBar> createState() =>
      _ScaffoldWithBottomNavBarState();
}

class _ScaffoldWithBottomNavBarState extends State<ScaffoldWithBottomNavBar> with AutomaticKeepAliveClientMixin  {
  late int _currentIndex = _locationToTabIndex(GoRouter.of(context).location);

  late List<ScaffoldWithNavBarTabItem> tabs = const [
    ScaffoldWithNavBarTabItem(
      initialLocation: "/",
      icon: Icon(Icons.sports_basketball),
      label: "Train",
    ),
    ScaffoldWithNavBarTabItem(
      initialLocation: "/progress",
      icon: Icon(Icons.insights),
      label: "Progress",
    ),
    ScaffoldWithNavBarTabItem(
      initialLocation: "/profile",
      icon: Icon(Icons.person),
      label: "Profile",
    ),
  ];

  int _locationToTabIndex(String location) {
    final index = tabs.indexWhere((t) => location.startsWith(t.initialLocation));
    return index < 0 ? 0 : index;
  }

  void _onItemTapped(BuildContext context, int tabIndex) {
    if (tabIndex != _currentIndex) {
      HapticFeedback.heavyImpact();
      context.go(tabs[tabIndex].initialLocation);
      setState(() {
        _currentIndex = tabIndex;
      });
    }
  }

  @override
  Widget build(BuildContext context) {
    super.build(context);
    return Scaffold(
      body: widget.child,
      bottomNavigationBar: Container(
        clipBehavior: Clip.hardEdge,
        decoration: BoxDecoration(
          borderRadius: BorderRadius.circular(24.0),
        ),
        child: BottomNavigationBar(
          currentIndex: _currentIndex,
          items: tabs,
          onTap: (index) => _onItemTapped(context, index),
          backgroundColor: Theme.of(context).colorScheme.primary,
          type: BottomNavigationBarType.fixed,
          selectedItemColor: Theme.of(context).colorScheme.secondary,
          unselectedItemColor: Colors.black26,
        ),
      )
    );
  }

  @override
  bool get wantKeepAlive => true;
}
