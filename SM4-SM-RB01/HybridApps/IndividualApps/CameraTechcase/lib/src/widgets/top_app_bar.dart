import 'package:flutter/material.dart';

import 'package:go_router/go_router.dart';

class CustomAppBar extends StatelessWidget implements PreferredSizeWidget {
  const CustomAppBar({this.title = "", Key? key}) : super(key: key);

  final String title;

  @override
  Widget build(BuildContext context) {
    return AppBar(
      leading: Padding(
        padding: const EdgeInsets.all(8.0),
        child: GoRouter.of(context).canPop() ? BackButton(
          color: Theme.of(context).colorScheme.onBackground,
          onPressed: () => GoRouter.of(context).pop(),
        ) : null,
      ),
      title: Text(title),
      centerTitle: true,
      elevation: 10,
      backgroundColor: Theme.of(context).colorScheme.primary,
    );
  }

  @override
  Size get preferredSize => const Size.fromHeight(kToolbarHeight);
}