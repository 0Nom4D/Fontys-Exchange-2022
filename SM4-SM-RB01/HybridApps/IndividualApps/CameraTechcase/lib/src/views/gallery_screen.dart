import 'package:flutter/material.dart';

import 'package:camera_techcase/src/widgets/gallery_grid.dart';
import 'package:camera_techcase/src/widgets/top_app_bar.dart';

class GridGallery extends StatefulWidget {
  const GridGallery({super.key});

  @override
  GridGalleryState createState() => GridGalleryState();
}

class GridGalleryState extends State<GridGallery> {
  @override
  Widget build(BuildContext context) {
    return const Scaffold(
      appBar: CustomAppBar(title: "GALLERY"),
      body: GalleryGrid(),
    );
  }
}