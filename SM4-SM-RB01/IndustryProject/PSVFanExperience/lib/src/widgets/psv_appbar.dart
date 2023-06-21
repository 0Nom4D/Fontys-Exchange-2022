import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:go_router/go_router.dart';

class PSVAppbar extends StatelessWidget implements PreferredSizeWidget {
  const PSVAppbar({Key? key, required this.title}) : super(key: key);

  final String title;

  @override
  Widget build(BuildContext context) {
    return AppBar(
      leading: Padding(
        padding: const EdgeInsets.all(8.0),
        child: GoRouter.of(context).canPop() ? BackButton(
          color: Theme.of(context).colorScheme.background,
          onPressed: () => GoRouter.of(context).pop(),
        ) : Image.asset(
          'assets/images/psvicon.png',
          width: 28,
          height: 23,
        ),
      ),
      title: Text(title),
      centerTitle: true,
      actions: [
        if (!GoRouter.of(context).location.endsWith('/profile'))
          Padding(
            padding: const EdgeInsets.all(8.0),
            child: GestureDetector(
              onTap: () {
                HapticFeedback.heavyImpact();
                GoRouter.of(context).go("${GoRouter.of(context).location == "/" ? "" : GoRouter.of(context).location}/profile");
              },
              child: CircleAvatar(
                child: Image.asset('assets/images/usericon.png'),
              )
            ),
          )
      ],
      elevation: 10,
      backgroundColor: Theme.of(context).colorScheme.primary,
    );
  }

  @override
  Size get preferredSize => const Size.fromHeight(kToolbarHeight);
}