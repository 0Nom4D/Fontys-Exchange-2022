import 'package:flutter/material.dart';
import 'package:go_router/go_router.dart';

class PSVDrawer extends StatelessWidget {
  const PSVDrawer({super.key});

  @override
  Widget build(BuildContext context) {
    return Drawer(
      backgroundColor: Theme.of(context).colorScheme.primary,
      child: Container(
        decoration: const BoxDecoration(
          image: DecorationImage(
            image: AssetImage('assets/images/DrawerBG.png'),
            fit: BoxFit.cover,
          ),
        ),
        child: ListView(
          shrinkWrap: true,
          padding: EdgeInsets.symmetric(vertical: MediaQuery.of(context).size.height * .15),
          children: [
            ListTile(
              title: Align(
                alignment: Alignment.centerRight,
                child: Text(
                  'PROFILE',
                  style: TextStyle(
                    color: Theme.of(context).colorScheme.background
                  ),
                )
              ),
              onTap: () {
                Scaffold.of(context).closeEndDrawer();
                GoRouter.of(context).go('/profile');
              },
            ),
            ListTile(
              title: Align(
                alignment: Alignment.centerRight,
                child: Text(
                  'SCAN SEASON PASS',
                  style: TextStyle(
                    color: Theme.of(context).colorScheme.background
                  ),
                )
              )
            ),
            ListTile(
              title: Align(
                alignment: Alignment.centerRight,
                child: Text(
                  'LANGUAGE',
                  style: TextStyle(
                    color: Theme.of(context).colorScheme.background
                  ),
                )
              )
            ),
            ListTile(
              title: Align(
                alignment: Alignment.centerRight,
                child: Text(
                  'LOGOUT',
                  style: TextStyle(
                    color: Theme.of(context).colorScheme.background
                  ),
                )
              )
            ),
          ],
        ),
      ),
    );
  }
}