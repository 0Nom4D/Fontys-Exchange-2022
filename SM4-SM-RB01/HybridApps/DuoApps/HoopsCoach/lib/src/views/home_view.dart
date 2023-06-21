import 'package:flutter/material.dart';

import 'package:app/src/widgets/image_button.dart';
import 'package:app/src/models/menus.dart';

class HomeView extends StatefulWidget {
  const HomeView({super.key});

  @override
  HomeViewState createState() => HomeViewState();
}

class HomeViewState extends State<HomeView> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        automaticallyImplyLeading: false,
        title: const Text(
            "",
            style: TextStyle(
              color: Colors.black,
              fontWeight: FontWeight.bold,
              fontSize: 40,
            )
        ),
        backgroundColor: Colors.transparent,
      ),
      body: Padding(
        padding: const EdgeInsets.symmetric(vertical: 10, horizontal: 15),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            const Text(
              "Training",
              textAlign: TextAlign.start,
              style: TextStyle(
                color: Colors.white,
                fontSize: 40,
                fontWeight: FontWeight.bold
              ),
            ),
            SizedBox(
              width: MediaQuery.of(context).size.width,
              height: MediaQuery.of(context).size.height * .68,
              child: ListView.separated(
                shrinkWrap: true,
                itemBuilder: (context, index) => ImageButton(
                  asset: MenuItem.menuItems[index].imageAsset,
                  text: MenuItem.menuItems[index].menuTitle,
                  toNavigate: MenuItem.menuItems[index].navigationLink,
                ),
                separatorBuilder: (context, index) => const SizedBox(height: 15),
                itemCount: 3
              )
            )
          ],
        )
      )
    );
  }
}
